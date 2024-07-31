"""
Implementation of the rewrite-based simple type system.
"""
from arsenal import colors
from itertools import combinations

from semirings import Boolean

from dyna.pretty import PrettyPrinter
from dyna.term import Term, fresh, vars, Subst, is_var, generalizer, deref, MostGeneralSet
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
            # the rule below is redundant, but it is in contrast to the "no free merge" case
            # $bound(X) :- $free(X), $bound(X).
            propagation_hooks = [self._propagation_hook_bound]
        )

        # Sometimes free and bound don
        self.cp_no_free_merge = ConstraintPropagation(
            rules + """
            $fail :- $free(X), $bound(X).
            """,
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

    def __call__(self, R, drop_checked=False, USE_INSTS=True, ALLOW_FREE_MERGE=True):
        assert isinstance(R, Rule), R
        R = deref(R)
        cp = self.cp_no_free_merge if not ALLOW_FREE_MERGE else self.cp

        chart = cp(R.body)
        if chart is None: return

        subst = Subst({x: y for _,x,y in cp.bindings})
        chart = {subst(x) for x in chart if isinstance(x, Term) and x.fn != '='}

        assert all(isinstance(x, Term) for x in chart)

        drop = set(cp.checked) if drop_checked else set()

        # The issue we have with intersection (i.e., the reason why we have 
        # ALLOW_FREE_MERGE=False) is that we actually do truly have intersection (subsumption 
        # actually) when we have a free variable.  It really is the case that f(X:free) is a
        # superset of f(X:int) and everything else!  So the behavior is correct.  The problem 
        # is that we are being sneaky with the not merging these free things.
        if USE_INSTS:

            bound_vars = {x.args[0] for x in chart if x.fn == '$bound'}
            free_vars = {x.args[0] for x in chart if x.fn == '$free'}
            got_bound = {X for X in bound_vars | free_vars if not is_var(X)}

            # drop $bound if its argument is already bound (equiv to dropping a checked constraint)
            for X in bound_vars & got_bound:
                drop.add(Term('$bound', X))

            if ALLOW_FREE_MERGE:
                # drop $free(X) if X is bound directly by unification or by any
                # non-$free constraint (equiv to dropping a checked constraint)
                for X in free_vars & got_bound:
                    drop.add(Term('$free', X))

                # (equiv to dropping a checked constraint)
                for X in free_vars:
                    #if not all((y.fn == '$free' or X not in vars(y)) for y in chart):   # <=== equivalent condition
                    if any((y.fn != '$free' and X in vars(y)) for y in chart):
                        drop.add(Term('$free', X))

            if not ALLOW_FREE_MERGE:

                # Fail when $free(X) has X is bound directly by unification or
                # by any non-$free constraint. Each free variables must be
                # distinct, otherwise they are not *free* they are *equality
                # constrained*.

                if free_vars & got_bound: return

                # We have a problem if there is more than 1 variable equal to `X`.
                if any(sum((X == A or X == B) for [_,A,B] in cp.bindings) > 1 for X in free_vars):
                    return

                if not all((y.fn == '$free' or X not in vars(y)) for y in chart for X in free_vars):
                    return

        return Rule(subst(R.head), *(chart - drop))

    def intersect(self, r, s, ALLOW_FREE_MERGE=False):
        "Compute the intersection of simple types `r` and `s`."
        s = fresh(s)
        assert isinstance(r, Rule) and isinstance(s, Rule), [r, s]
        subst = Subst().mgu(r.head, s.head)
        if subst is Subst.FAIL: return None
        return self(Rule(r.head, *r.body, *s.body, *scons(subst)),
                    ALLOW_FREE_MERGE=ALLOW_FREE_MERGE)

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
        T = self(t, ALLOW_FREE_MERGE=False, drop_checked=True)

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

    # TODO: If r ⊇ s then the anti-unifier should be equivalent to r
    def anti_unifier(self, r, s):
        "Return a simple type `t` such that `t ⊇ r and t ⊇ s` if `r` and `s` might overlap."

        r = fresh(r)
        s = fresh(s)

        new_head = generalizer(r.head, s.head)

        # substitution constraints
        r_subst = scons(Subst().mgu(r.head, new_head))
        s_subst = scons(Subst().mgu(s.head, new_head))

        R = self.cp({*r.body, *r_subst})
        checked = set(self.cp.checked)

        S = self.cp({*s.body, *s_subst})
        checked |= set(self.cp.checked)

        if S is None: return r
        if R is None: return s

        [T] = Program([Rule(new_head, *(set(S) & set(R)))], semiring=Boolean).snap_unifications()

        TT = Rule(T.head, *{
            x for x in T.body
            if vars(x) <= vars(T.head)   # drop existentially quantified constraints
            and len(vars(x)) > 0         # drop constraints that have no variables (they didn't fail, so assume they are true)
            and x not in checked         # already checked
            and not (isinstance(x, Boolean) and x.score)
        })

        if DEBUG > 2:

            print = PrettyPrinter().print
            print()
            print(colors.orange % '= ANTI-UNIFIER ====')
            print('r=', r)
            print('s=', s)
            for x in set(S) - set(R):
                print('  ', colors.light.red % 's-r:', x)
            for x in set(S) & set(R):
                print('  ', colors.mark(True), x)
            for x in set(R) - set(S):
                print('  ', colors.light.red % 'r-s:', x)

            #print('new head:', new_head)
            #print('subst:', subst)
            print('t=', colors.render(colors.orange % T))
            print('checked:', checked)

            print(colors.orange % 'FINAL', TT)

        return TT
