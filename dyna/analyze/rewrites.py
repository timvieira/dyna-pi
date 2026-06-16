"""
Implementation of the rewrite-based simple type system.
"""
from arsenal import colors
from itertools import combinations

from dyna.pretty import PrettyPrinter
from dyna.term import Term, fresh, term_vars, Subst, generalizer, deref, MostGeneralSet
from dyna.program import Program, Rule
from dyna.propagate import ConstraintPropagation, scons

# We can encode fundeps with this scheme.  For example,
# W=W' :- word(W,I,J), word(W',I,J').
# sum(1,I,J) :- word(W,I,J).
#
# which together with a fundep on sum implies that the first rule's body also implies J=J'
#
# _ :- n("ROOT").  means that n("ROOT") is a contradiction (we can derive all constraints, so the type is empty).
# This branch is not very useful in backward chaining, though.   Using it to elaborate a type will just result in an empty branch of that type.
# The point of writing this is just to show that we don't need to create special fail head for such rules.
# In practice, I think we should use the syntactic sugar !n("ROOT").
# (or ~n("ROOT") if we think ! looks too confusingly like an assertion).

DEBUG = 0
STOP_ON_ERROR = False


class Rewrites:

    def __init__(self, rules):
        self.cp = ConstraintPropagation(
            rules,
            propagation_hooks = [self._propagation_hook_bound]
        )

    @staticmethod
    def _propagation_hook_bound(cp, driver):
        # XXX: bound means ground...
        def rec_bound(x):

            # TODO: clean up this method so that it doesn't have this rec_bound
            # helper.  I think we can use ordinary recursion
            # (_propagation_hook_bound -> _propagation_hook_bound).

            if not isinstance(x, Term): return
            if x.fn != '$bound': cp.update(Term('$bound', x))
            for y in x.args: rec_bound(y)

        if isinstance(driver, Term) and driver.fn == '$bound':
            rec_bound(driver)

    def __repr__(self):
        return f'{self.__class__.__name__} {Program(self.cp.rules)}'

    def __call__(self, R, drop_checked=False):
        assert isinstance(R, Rule), R
        R = deref(R)

        chart = self.cp(R.body)
        if chart is None: return

        subst = Subst({x: y for _,x,y in self.cp.bindings})
        chart = {subst(x) for x in chart if isinstance(x, Term) and x.fn != '='}

        assert all(isinstance(x, Term) for x in chart)

        drop = set(self.cp.checked) if drop_checked else set()

        return Rule(subst(R.head), *(chart - drop))

    def intersect(self, r, s):
        "Compute the intersection of simple types `r` and `s`."
        s = fresh(s)
        assert isinstance(r, Rule) and isinstance(s, Rule), [r, s]
        subst = Subst().mgu(r.head, s.head)
        if subst is Subst.FAIL: return None
        return self(Rule(r.head, *r.body, *s.body, *scons(subst)))

    def covers(self, r, s):
        "Return true if `r ⊇ s`"

        subst = Subst().mgu(r.head, s.head)
        if subst is Subst.FAIL: return

        # substitution constraints
        sc = scons(subst)

        # specialize the r rule to match s's head.
        R = self(Rule(r.head, *r.body, *sc), drop_checked=True)
        S = self(s, drop_checked=True)

        t = Rule(r.head, *s.body, *r.body, *sc)
        T = self(t, drop_checked=True)

        if DEBUG > 2:
            head_cond = S is not None and T is not None and s.head == T.head
            body_cond = S == T == None or (T is not None and S is not None) and set(S.body) >= set(T.body)
            cond = head_cond and body_cond

            print = PrettyPrinter().print
            print()
            print('= COVERS ====')
            print(subst)
            print('r=', r)
            print('s=', s)
            print('t=', t)
            print('---')
            print('R=', R)
            print('S=', S)
            print('T=', T)
            print('---')
            print('head-cond:', head_cond)
            print('body-cond:', body_cond)
            print('overall', cond)
            print('=============')

        if S is None: return True
        if R is None: return False
        if T is None: return False

        return S.head == T.head and set(S.body) >= set(T.body)

    def same(self, r, s):
        return self.covers(r, s) and self.covers(s, r)  # pylint: disable=W1114

    def disjoint(self, r, s):
        return self.intersect(r, s) is None

    def dedup(self, p):
        """
        Remove redundant simple types in `p`.  A simple type r ∈ p is redundant
        if ∃ s ∈ p : s ⊇ t.
        """
        assert isinstance(p, Program), p
        new = MostGeneralSet(p, self.covers)
        return p.spawn(new.xs)

    # TODO: use the hash-bucketing trick to speed this up.
    def disjoin(self, p):
        "Return an disjoint estimate of p."
        tmp = set(p)
        while True:
            for r, s in combinations(tmp, 2):
                if self.intersect(r, s):
                    t = self.anti_unifier(r, s)
                    tmp.remove(r)
                    tmp.remove(s)
                    tmp.add(fresh(t))
                    break
            else:
                return p.spawn(tmp)

    def anti_unifier(self, r, s):
        "Return a simple type `t` such that `t ⊇ r and t ⊇ s` if `r` and `s` might overlap."

        r = fresh(r)
        s = fresh(s)

        new_head = generalizer(r.head, s.head)
        head_vars = term_vars(new_head)

        # Propagate each body onto the shared generalized head.
        R = self.cp({*r.body, *scons(Subst().mgu(r.head, new_head))})
        S = self.cp({*s.body, *scons(Subst().mgu(s.head, new_head))})

        # If either side is unsatisfiable then it contributes no constraints to
        # the overlap, so the other side covers it.
        if R is None: return s
        if S is None: return r

        # Candidates are the propagated constraints expressed purely over the
        # generalized head's variables.  A candidate belongs in the anti-unifier
        # iff it is entailed by *both* r and s.  We test entailment with
        # `covers` rather than by intersecting the two charts directly: the
        # latter matches constraints by exact term equality and so drops a
        # constraint such as r's `ks(Xs)` whenever s states the equivalent fact
        # in a different shape (e.g. `k(Y2), ks(Ys)` for the tail `[Y2|Ys]`).
        # Because every constraint of r passes this test when r ⊇ s, the result
        # is then equivalent to r (and symmetrically for s ⊇ r).
        candidates = {
            x for x in set(R) | set(S)
            if isinstance(x, Term)
            and x.fn not in {'=', '$bound', '$free'}
            and len(term_vars(x)) > 0         # drop ground, existential constraints (i.e., assume they succeed)
            and term_vars(x) <= head_vars     # keep only head-connected constraints
        }

        body = {
            A for A in candidates
            if self.covers(Rule(new_head, A), r) and self.covers(Rule(new_head, A), s)
        }

        t = Rule(new_head, *body)

        if DEBUG > 2:
            print = PrettyPrinter().print
            print()
            print(colors.orange % '= ANTI-UNIFIER ====')
            print('r=', r)
            print('s=', s)
            for A in candidates:
                kept = A in body
                print('  ', colors.mark(kept), A)
            print(colors.orange % 'FINAL', t)

        return t
