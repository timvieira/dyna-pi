from dyna import (
    fresh, term_vars, TransformedProgram, Rule, Derivation, Product, Constant
)
from functools import cached_property


class Unfold(TransformedProgram):
    def __init__(self,
                 program: 'Parent program',
                 i: 'Index of rule to inline into',
                 j: 'Index of subgoal to inline',
                 defs: 'program to inline from' = None,
    ):

        assert isinstance(i, int) and isinstance(j, int), [i, j]

        self.i = i
        self.j = j
        self.r = r = program.rules[i]

        if defs is None: defs = program
        self.defs = defs

        if 0:

            # Unfortunately, we can't yet switch over to the new version.
            # because the bookkeeping (S and rule.i) are used for megafold.
            #
            # Also, many tests and notebooks will break if we change the order
            # of rules

            p = program
            r = p[i]
            u = p - {i}   # remove the rule
            u[r.head] = Constant(r.body[:j]) * defs.q(r.body[j]) * Constant(r.body[j+1:])
            super().__init__(f'Unfold({self.i}, {self.j})', program, u)

            # We are running into a couple problems, due to constant folding in
            # the new school things...

            #self.S = u[len(p)-1:]
            #n = len(p)-1
            #for s, ss in zip(self.S, defs.lookup(r.body[j])):#defs.q(r.body[j])):
            #    s.i = ss.i
            #    s.ii = n
            #    n += 1
            #    print(n)

        else:
            # Below, we split the RHS factors into `left` and `right` products to
            # keep the the revised RHS in the same order.

            new = list(program.rules)
            new.remove(r)

            assert defs.safe_inline(r.body[j]), f"unsafe to unfold `{r.body[j]}` at ({i},{j}) against definitions {self.defs}."

            self.new2def = {}
            for s in defs.lookup(r.body[j]):

                t = Rule(r.head, *r.body[:j], *s.body, *r.body[j+1:])

                # Check if we lost a variable.
                if not (set(term_vars(s)) <= set(term_vars(t))):
                    m = program.Semiring.multiple(inf)
                    if m != program.Semiring.one:
                        t = Rule(t.head, *t.body, m)

                t = fresh(t)
                ii = len(new)   # index of the new rule t in the new program
                new.append(t)
                self.new2def[ii] = s.i  # index of the rule that we unfolded in defs (None for builtins)

            self.def2new = {y: x for x,y in self.new2def.items()}

            super().__init__(f'Unfold({self.i}, {self.j})', program, new)

    @cached_property
    def undo(self):
        # Note: self.r = self.parent[self.i]
        return self.manual_fold(r=self.r, j=self.j, S=self.new2def, defs=self.defs)

    def transform(self, d):
        if isinstance(d, (Product, tuple, list)):
            return Product([self.transform(x) for x in d])
        elif Derivation.base(d):
            return d
        elif d.i == self.i:   # the unfolded rule
            assert d.p == self.parent
            d_left, d_middle, d_right = d.body[:self.j], d.body[self.j], d.body[self.j+1:]
            d_middle_defs = self.Transform(d_middle, self.defs)
            d_middle_new = self.defs.Transform(d_middle_defs.body, self.parent)
            new_rule_ix = self.def2new[d_middle_defs.i]
            return self.d(new_rule_ix)(d.head, *self.transform(d_left * d_middle_new * d_right))
        else:
            assert d.p == self.parent
            I = self.rules.index(d.R)   # figure out the index of the copied rule in the new program
            return self.d(I)(d.head, *self.transform(d.body))

#    def _untransform(self, d):
#        rule = d.__rule__
#        body = d.body
#        assert d.p == self
#        if rule in {self[i] for i in self.new2def}:  # rules that replaced by the unfold
#            tmp = self.defs[self.new2def[d.i]]
#            # all of these folds give the same new rule (self.r)
#            [r] = d.r.folds_by(tmp)
#            s = self.defs.d(self.new2def[d.i])(
#                tmp.head/r.subst,
#                *body[sorted(r.align)].transform(self.defs)
#            )
#            left = body[[i for i in r.remaining if i <= self.j]]
#            right = body[[i for i in r.remaining if i > self.j]]
#            body = left * s * right
#            rule = self.r
#            I = self.i
#        else:
#            I = self.parent.rules.index(rule)
#        return self.parent.d(I)(d.head, *body.transform(self.parent))

    def untransform(self, d):
        # implementation shortcut: use the undo (fold) program's derivation mapping
        return self.undo.Transform(self.undo.transform(d), self.parent)

    def compute_measure(self, M):
        "Fold-unfold safety measure for this (generalized) unfold. `M` is the Measure context."
        # Common-ancestor precondition; see Fold.compute_measure for rationale.
        assert self.parent.root is self.defs.root, (
            f"Unfold's parent and defs must share a root program "
            f"(got parent.root id={id(self.parent.root)}, "
            f"defs.root id={id(self.defs.root)}). Build defs via "
            f"`<root>.define(rule_text)` against the unfold's root."
        )
        # Freshness precondition (returns unsafe measure rather than raising;
        # see Fold.compute_measure for rationale).
        if M._freshness_violations(self.parent, self.defs):
            return M.zero_measure(self)

        m_new = [None]*len(self)
        m_parent = M(self.parent); m_defs = M(self.defs)

        for N, r in enumerate(self):
            if N in self.new2def:
                m_new[N] = m_parent.m[self.i] + m_defs.m[self.new2def[N]]
            else:
                m_new[N] = m_parent.m[self.parent.rules.index(r)]

        # Check the safety conditions for generalized unfold.
        P = self.i
        safe = m_parent._safe + m_defs._safe
        for (_,D) in self.new2def.items():
            # don't count the size of the subgoal that we replaced in the unfold action
            extra = M.min_size(self.parent.rules[P].body[:self.j]) + M.min_size(self.parent.rules[P].body[self.j+1:])
            safe.append(
                    (m_parent.m[P] + m_defs.m[D]).lo + extra > 0
            )
        return M.safety(m_new, self, safe)



inf = float('inf')
