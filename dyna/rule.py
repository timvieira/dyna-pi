from arsenal import colors
from collections import Counter
from dyna.term import Term, vars, same, canonicalize, fresh, snap, Var, Product, Subst, FAIL

from functools import cached_property, lru_cache
from collections import defaultdict
from dyna.util import FrozenBag, OrderedSet

def fn(x): return x.fn if isinstance(x, Term) else x


#def term_signature(x):
#    return canonicalize(x)
#    return Term(x.fn, x.arity) if isinstance(x, Term) else Term("$const", x)
def term_signature(x):
    # Need to wrap constants in term to use the right comparison operation...
    return canonicalize(x) if isinstance(x, Term) else Term("$const", x)


def is_const(x):
    return not isinstance(snap(x), (Var, Term))


class Rule(Term):
    """
    Rule is a pair of a `head` and a `body`, which may contain variables.
    The `body` is a `Product` of subgoals.
    """

    # WARNING: This rule caches some quantities (folds_by, signature, equality),
    # which will become stale if the variables in this rule are mutated through
    # unification.

    def __init__(self, head, *body):
        self.head = head
        self.body = Product(body)
        super().__init__(head, *body)

    @cached_property
    def analyzer(self):
        return RuleAnalyzer_(self)

    def lift(self, semiring):
        "Lift constant values into `semiring`"
        if semiring is None: return self
        return Rule(self.head, *[semiring.lift(x, self.head) if is_const(x) else x
                                 for x in self.body])

    def is_const(self):
        "Doe this rule's body only contain constant values?"
        return sum(not is_const(y) for y in self.body) == 0

    def is_linear(self):
        "Is this rule linear (i.e., does it have at most one subgoal)?"
        return sum(not is_const(y) for y in self.body) == 1

    #___________________________________________________________________________
    # Equality

    # We could inline constants, e.g., f(3, Y) -> (3, None), or something similar;
    # Note that if we want argument order invariance, we'd have to sort the tuple.
    @cached_property
    def signature(self):
        "Compute rule signaure"
        return (term_signature(self.head), FrozenBag(term_signature(x) for x in self.body))

    @cached_property
    def _body_fns(self):
        return Counter([fn(x) for x in self.body])

    @cached_property
    def _hash_cache(self):
        return hash(self.signature)

    def same(self, other):
        "Rule equality modulo variable renaming and subgoal reordering."
        if self is other: return True
        if self._hash_cache != other._hash_cache: return False
        #if self.signature != other.signature: return False
        if not vars(self).isdisjoint(vars(other)): other = fresh(other)
        s = Subst().cover(self.head, other.head)
        return any(
            (s != FAIL and s.is_non_specializing() and s(self.head) == other.head)
            for s in self.body._match_comm(
                    other.body, 0,
                    frozenset(range(len(other.body))),
                    s,
            )
        )

    def round(self, precision):
        return Rule(self.head, *[round(x, precision) if is_const(x) else x
                              for x in self.body])

    #___________________________________________________________________________
    # Utils / Manipulation / Inference / Transformation

    def unfold(self, j, defs):
        return self.to_program().unfold(0, j, defs=defs)

    def to_program(self):
        from dyna import Program
        return Program([self])

    @lru_cache
    def folds_by(self, r):

        folds = set()

        for (subst, align, remaining) in r.body.covers(self.body):
            R = subst(r)
            #assert subst(s) == s

            rest = Product([self.body[k] for k in remaining])

            # [2022-03-05 Sat] The junk-binding trick: If `r` is
            # non-range-restricted and we don't bind any of its head variables,
            # we can end up with unwanted infinite multiplicity.  Our workaround
            # is to bind the variable to an arbitrary "junk" value.
            #
            # Here is an example:
            #
            #   goal += b(X) * c(X) * d(Z).
            #   foo(X,Y) += b(X) * c(X).   % Y is free
            #
            # Without this trick, we'll try the following fold
            #
            #   goal += f(X,Y) * d(Z).
            #
            # which we have to reject because unfolding it will introduce an
            # unwanted infinite multiplicity due to the Y variable (that wasn't
            # in the original rule).
            #
            #   goal += b(X) * c(X) * inf * d(Z).
            #
            # As a general rule, fold should never introduce a variable - it
            # should only drop variables (by pushing them into the folder).
            #
            annoying_var = (vars(R.head) - vars(R.body)) - vars(rest)
            if 0: print('annoying_var:', annoying_var)
            R = Subst({v: "junk" for v in annoying_var})(R)

            t = FoldedRule(

                head = self.head,
                left = Product(),
                subgoal = R.head,
                right = rest,

                folded = self,
                folder = r,
                subst = subst,
                align = align,
                remaining = sorted(remaining)

            )

            #assert vars(t) <= vars(self), 'should not happen'

            # Safety check: reversibility condition, this is much slower
            # because of copy-overhead and equality testing
            #from dyna import Program
            #[foo] = t.unfold(0,defs=Program([r]))
            #safe = foo.same(self)

            # Safety check: variable-locality condition. Folds should not
            # bind r-locals and should not introduce variables (it would
            # messing up the multiplicity).
            V_inside = vars(R.body) - vars(R.head)
            V_outside = vars(self.head) | vars(rest)

            if V_inside.isdisjoint(V_outside):
                folds.add(t)

        return folds


# Rule with lots of bookkeeping
# TODO: I don't like this class, we should keep bookkeeping elsewhere.
class FoldedRule(Rule):

    def __init__(self, head, left, subgoal, right,
                 folded, folder, subst, align, remaining):

        self.left = left
        self.subgoal = subgoal
        self.right = right

        super().__init__(head, *left, subgoal, *right)

        self.folded = folded
        self.folder = folder
        self.subst = subst
        self.align = align
        self.remaining = remaining

        self.j = len(self.left)

    def fresh(self, m):
        return FoldedRule(
            m(self.head),
            m(self.left),
            m(self.subgoal),
            m(self.right),
            folded=self.folded,
            folder=self.folder,
            subst=self.subst,
            align=self.align,
            remaining=self.remaining,
        )

    def sub(self, s):
        return FoldedRule(
            s(self.head),
            s(self.left),
            s(self.subgoal),
            s(self.right),
            folded=self.folded,
            folder=self.folder,
            subst=self.subst,
            align=self.align,
            remaining=self.remaining,
        )


class RuleAnalyzer_:
    def __init__(self, r):
        #assert isinstance(r, Rule), r
        out_vars = vars(r.head)
        # map from variables to factors
        vs = vars(r)
        v2f = {v: [] for v in vs}
        fs_with_vars = OrderedSet()        # indices of factors that contain at least one variable
        for i, x in enumerate(r.body):
            for v in vars(x):
                v2f[v].append(i)
                fs_with_vars.add(i)

        # only counting factors -- i.e., subgoals, which must be the rhs.
        self.v2f = v2f
        self.rule = r
        self.head = r.head
        self.vs = vs
        self.body_vars = vars(r.body)
        self.local_vars = vs - out_vars
        self.out_vars = out_vars
        self.degree = len(vs)

        # If there is a factor that every local variable depends on, then we
        # cannot eliminate any variable.  For example,
        # hadamard products like f(X,Y) * g(X,Y) have no variables to eliminate
        # goal(X,Y,Z) += f(X,Y,Z) also has no variables we can eliminate
        can_elim = OrderedSet()
        for v in self.local_vars:
            if set(self.v2f[v]) < set(fs_with_vars):
                can_elim.add(v)
        self.can_elim = can_elim

    def __repr__(self):
        return f'RuleAnalyzer(`{self.rule}`, degree={self.degree}, can_elim={self.can_elim})'
