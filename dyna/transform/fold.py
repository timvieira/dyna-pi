from collections import Counter
from functools import cached_property

from dyna import TransformedProgram, Derivation, Product, Term, Subst

DEBUG = 0


class Fold(TransformedProgram):
    def __init__(self,
                 *,
                 defs: 'auxiliary definitions',
                 parent: 'parent in transformation sequence',
                 r: 'new rule',
                 S: 'rules in parent to be replaced',
                 j: 'subgoal index in r',
    ):
        if defs is None: defs = parent

        self.r = r
        self.i = 0
        self.j = j
        self.S = S
        self.defs = defs
        super().__init__(f'Fold({r.__repr__(color=False)!r})', parent, [r] + list(parent - S))
        assert self.rules[self.i] == self.r

    @cached_property
    def partially_safe(self):
        "Check the reversibility condition"
        return self.parent == self.u

    @cached_property
    def safe_by_rev(self):
        # Note: this is not the same as the unfolded program (u).
        return self.rev == self.parent

    @cached_property
    def u(self):
        "Unfold the folded program against the definitions."
        return self.unfold(i=self.i, j=self.j, defs=self.defs)

    @cached_property
    def rev(self):
        "Unfold the folded program against itself."
        return self.unfold(i=self.i, j=self.j, defs=None)

    @cached_property
    def undo(self):
        if not self.partially_safe:
            return self.rev
        else:
            return self.u

    @cached_property
    def par2def(self):
        "Alignment: `self.parent` to `self.undo`."
        return {P: D for D,P in self.def2par.items()}

    @cached_property
    def def2par(self):
        "Alignment: `self.undo` to `self.parent`."
        [def2par, _] = self.__align_to_parent
        return def2par

    @cached_property
    def bookkeeping(self):
        "Additional information about the alignment `self.parent` to `self.undo`"
        [_, bookkeeping] = self.__align_to_parent
        return bookkeeping

    @cached_property
    def __align_to_parent(self):
        """
        Align rules in `self.undo` to rules in parent program.
        """

        # If the fold isn't partially safe, then it is probably reversible,
        # this has a different alignment but the code to handle both cases is the same.
        rev = self.undo

        # new <===> (defs <===> rev <===> par)
        def2rev = rev.def2new

        # Reverse engineer the alignment between `defs` and `parent` that gives
        # rise to `self` after folding. We use the fact that
        #     parent == new.unfold(i, j, defs) == rev
        rev2par = dict(rev.align(self.parent))

        bookkeeping = {}; def2par = {}
        for D,R in def2rev.items():   # note: unfold.new2def is def2new for us
            P = rev2par[R]
            # NOTE: R and P are [deep] equal, but R may have reorder subgoals.
            # crude version parent.folds_by(...)
            for t in self.parent.rules[P].folds_by(self.defs.rules[D]):
                bookkeeping[P] = t
            #assert self.parent[P].same(rev[R])
            #assert D not in def2par   # test should actually be for bijection this is just one side
            def2par[D] = P

        return (def2par, bookkeeping)

    def transform(self, d):
        def node(n):
            if n.i not in self.S:              # top rule was copied to new program
                assert n.p == self.parent
                I = self.rules.index(n.R)   # the index of the copied rule in the new program
                return self.d(I)(n.head, *self.transform(n.body))
            # rules that were replaced by the fold
            assert n.p == self.parent

            if not self.partially_safe:
                return self.rev.Transform(self.Transform(n, self.rev), self.rev.undo)

            # We have recorded that the top rule P of this derivation maps
            # [via par2def] to a defining rule D.
            def_rule_ix = self.par2def[n.i]
            def_rule = self.defs.rules[def_rule_ix]

            # Use our recorded alignment of P's subgoals to D's subgoals
            bookkeeping = self.bookkeeping[n.i]

            # Note: Splitting uses some guess work to determined left vs. right
            d_left = n.body[[i for i in bookkeeping.remaining if i <= self.j]]
            d_middle = n.body[list(sorted(bookkeeping.align))]
            d_right = n.body[[i for i in bookkeeping.remaining if i > self.j]]

            # determine the unique substitution that makes the body of the
            # derivation match the body of def_rule
            θ = Subst()
            for i, j in bookkeeping.align.items():
                θ.cover(def_rule.body[j], n.r.body[i])

            # The middle is where all the action happens
            d_middle_new = self.defs.Transform(self.defs.d(def_rule_ix)(
                θ(def_rule.head), *self.Transform(d_middle, self.defs)
            ), self.parent)

            return self.d(self.i)(n.head, *self.transform(d_left * d_middle_new * d_right))
        return Derivation.map(d, node)

    def untransform(self, d):
        # implementation shortcut: use the undo (unfold) program's derivation mapping
        return self.undo.Transform(self.undo.transform(d), self.parent)

    def compute_measure(self, M):
        "Fold-unfold safety measure for this (generalized) fold. `M` is the Measure context."
        assert self.partially_safe
        # Common-ancestor precondition. The fold's rule-measure relations only
        # make sense if `parent` and `defs` descend from the same root program
        # (so their measure variables were allocated against a shared rule-index
        # basis). Build defs via `<root>.define(rule_text)` where <root> is the
        # same root program as the fold's parent. We KEEP this as an assertion
        # because failing it indicates a usage error (not a safety verdict) —
        # the measure simply cannot be computed when measure-variable bases differ.
        assert self.parent.root is self.defs.root, (
            f"Fold's parent and defs must share a root program "
            f"(got parent.root id={id(self.parent.root)}, "
            f"defs.root id={id(self.defs.root)}). Build defs via "
            f"`<root>.define(rule_text)` against the fold's root."
        )
        # Freshness precondition: any rule in `defs` not already in `parent`
        # (and not in the shared root) introduces an equation the algebra
        # cannot verify against parent's existing definitions. Return an
        # unsafe measure rather than raising, so search/filter pipelines
        # using `m.safe` reject these candidates cleanly.
        if M._freshness_violations(self.parent, self.defs):
            return M.zero_measure(self)
        m_new = [None]*len(self)
        m_parent = M(self.parent); m_defs = M(self.defs)
        diffs = [m_parent.m[P] - m_defs.m[D] for P,D in self.par2def.items()]
        m_r = M.Interval(M.Min([x.lo for x in diffs]), M.Max([x.hi for x in diffs]))
        for N, r in enumerate(self):   # TODO: can't we do this without a loop?
            if N == self.i:
                m_new[N] = m_r
            else:
                m_new[N] = m_parent.m[self.parent.rules.index(r)]   # TODO: is/can this index tracked in the transformation metadata?
        # Check the safety conditions for generalized fold.
        safe = m_parent._safe + m_defs._safe
        for (D,P) in self.def2par.items():
            extra = M.min_size(self.bookkeeping[P].left) + M.min_size(self.bookkeeping[P].right)
            safe.append(
                (m_parent.m[P] - m_defs.m[D]).lo + extra > 0
            )
        return M.safety(m_new, self, safe)


def term_signature(x):
    return (x.fn,x.arity) if isinstance(x, Term) else None


# The utility is only used by reversible folds which appear to require searching
# for the set of rules that are replaced.
def prune_r_S(Q, r):

    # pruning: Given that the set of rule pairs
    #
    #   {(A += L1 * R, B += L0)}
    #
    # Turns into a single rule: A += B * R.
    #
    # We need the As and Bs and Rs to plausibly match. A little lookahead at
    # the number of subgoals and rules could prune away a lot of failed
    # matches!

    A = term_signature(r.head)
    B = term_signature(r.body[r.j])

    R = Counter([term_signature(b) for b in r.body])
    R[B] -= 1   # u's body is B * R
    if R[B] == 0: R.pop(B)

    # S is the set of candidate that the rule u may be able to replace
    S = set()
    for j in range(len(Q)):
        if term_signature(Q.rules[j].head) == A:
            LR = Counter([term_signature(b) for b in Q.rules[j].body])
            if all(LR[b] >= R[b] for b in R):  # has enough of R's subgoals
                S.add(j)

    return S


# at most one answer
class memoize1:

    def __init__(self, f):
        self.memos = {}
        self.k = 0
        self.n = 0
        self.f = f

    def __call__(self, *key):
        self.n += 1
        val = self.memos.get(key)
        if val is None:
            val = set()
            for x in self.f(*key):
                val.add(x)
                break
#            self.memos[key] = val = set(self.f(*key))   # materialize iterator, remove duplicates
            self.memos[key] = val
#            assert len(val) <= 1
        else:
            self.k += 1   # cache hit
        return val

    def __repr__(self):
        return f'<memoized {self.f.__name__}, hitrate={self.k/self.n:.1%}, hits={self.k}, calls={self.n}>'


def fold_r_S(parent, defs, r, Qs):
    "Search for the subsets S ⊆ parent that could be replaced by `r`."

    @memoize1
    def f(S):
        # We are free to try the unfolding whenever, but it will probably fail
        # unless we have grabbed all of the rules in P that we need.
        new = Fold(parent=parent, r=r, S=S, defs=defs, j=r.j)
        if new.safe_by_rev: yield new
        for i in S: yield from f(S - {i})

    for new in f(frozenset(Qs)):
        yield new
        return
