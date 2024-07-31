
from dyna import (
    syntax, Derivation, Rule, Product, Term, TransformedProgram,
    fresh, covers, unifies, unify, not_matches3
)


class Slash(TransformedProgram):

    def __init__(self,
                 program,
                 x: 'item to be slashed out',
                 positions: 'positions to slash from {rule id: subgoal index}',
                 other_fn = '$other',
                 slash_fn = '/',
    ):

        assert program.inputs is not None
        if isinstance(x, str): x = syntax.term(x)

        # Below, we check that `slash_fn` and `other_fn` are unique symbols in
        # `program`.  (Note that this is stricter than necessary, what we need
        # is for the types generated by the slash to be disjoint with existing
        # types, e.g., (f(X)/foo) is distinct from (f(X)/goo) even though their
        # outer functors are the same.
        slash_fn = program._gen_functor(slash_fn)
        other_fn = program._gen_functor(other_fn)

        # x must have unique variables
        x = fresh(x)

        self.x = x
        self.positions = positions
        self.parent = program
        self.other_fn = other_fn
        self.slash_fn = slash_fn
        slash = self._slash; other = self._other

        self._parent_nodes = nodes = program._coarse_graph().nodes

        new_rs = []
        def add_rule(*xs):
            r = fresh(Rule(*xs))
            new_rs.append(r)
            return r

        # TODO: use a better data structure (e.g., union of nonground terms) to
        # represent this.
        useful_other = [self.x]
        for i, r in enumerate(program):
            j = self.positions.get(i)
            if j is not None:
                y = program.rules[i].body[j]
                if self.is_const(y) or self.is_builtin(y):
                    nodes.add(y)      # add to the set of nodes
                else:
                    useful_other.append(y)

        self._useful_other = useful_other

        # there are 6 kinds of rules: ss, oo, o, rso, ro, base
        self.ss = {}; self.rso = {}; self.ro = {}; self.o = {}; self.oo = {}

        self.base = add_rule(slash(x, x))     # needed only if x

        for i, r in enumerate(program):

            j = positions.get(i)

            h = r.head; b = r.body

            if j is None:
                if self._is_useful_other(h):
                    self.o[i] = add_rule(other(h), *b)
                else:
                    # don't create useless `$other` items
                    self.o[i] = add_rule(h, *b)

                continue

            # Check conditions on position vector
            assert not unifies(x, r.body[j]) or covers(x, r.body[j])
            assert not len(r.body) == 0
            #assert not program.is_builtin(b[j]), b[j]
            #assert not program.is_const(b[j]), b[j]

            self.ss[i] = add_rule(slash(h, x), *b[:j], slash(b[j], x), *b[j+1:])

            if not unifies(self.x, b[j]):
                self.oo[i] = add_rule(other(h), *b[:j], other(b[j]), *b[j+1:])

#            self.oo[i] = add_rule(other(h), *b[:j], *not_matches2(x, b[j]), other(b[j]), *b[j+1:])

        # Below, we generate rules for each of the possible functors.  (This is
        # required for our trick which enables us to not label inputs with
        # other.)

        for y in nodes:

            if program.is_exogenous(y):
                continue

            y = fresh(y)

            if self._is_useful_other(y):
                for c in not_matches3(fresh(self.x), y):
                    self.ro[y] = add_rule(y, other(y), *c)

            for x in nodes:
                x = fresh(x)
                for _ in unify(self.x, x):
                    self.rso[y,x] = add_rule(y, other(x), slash(y, x))

        super().__init__(('slash', x), program, new_rs)

        # XXX: quick hack to put rule indices on rules...
        for i,r in enumerate(self):
            r._index = i

    def _slash(self, y, x):
        #assert not self.is_const(x), x
        return Term(self.slash_fn, y, x)

    def _other(self, x):
        # No need to wrap the input in other(...).  We don't need these
        # items because the item x that we are slashing out cannot appear in
        # an input's computation (bc no items can!).  In other words, a
        # little bit of program tidying would clean this up for us, but I'd
        # rather not make more of a mess than necessary.
        #assert not self.is_const(x), x
        if self.parent.is_exogenous(x):
            return x
        elif self._is_useful_other(x):
            return Term(self.other_fn, x)
        else:
            return x

    def _is_useful_other(self, x):
        return any(unifies(x, y) for y in self._useful_other)

    def tidy(self, **kwargs):
        # Check that the slashed based case is indeed the first rule.
        assert self.rules[0].head.fn == self.slash_fn, p
        return self.elim_p(0, **kwargs)

    def transform(self, d):

        if isinstance(d, (list, tuple, Product)):
            return Product(map(self.transform, d))

        if Derivation.base(d):
            return d

        #tree = self.d(None)
        coarsen = self._parent_nodes.root
        slash = self._slash
        frozen = self._other
        is_frozen = lambda x: isinstance(x, Term) and x.fn == self.other_fn

        getx = lambda o: (o.head.args[0] if is_frozen(o.head) else o.head) if isinstance(o, Derivation) else o

        D_ro = lambda head, *body: self.d(self.ro[coarsen(head)]._index)(head, *body)
        D_ro = lambda head, *body: self.d(None)(head, *body)
        D_rso = lambda head, o, *body: self.d(self.rso[coarsen(head), coarsen(o.head.args[0]) if isinstance(o, Term) else o]._index)(head, o, *body)
        D_rso = lambda head, o, *body: self.d(None)(head, o, *body)
        D_ss = lambda d: self.d(self.ss[d.i]._index)
        D_oo = lambda d: self.d(self.oo[d.i]._index)
        D_base = self.d(self.base._index)
        D_o = lambda d: self.d(self.o[d.i]._index)

        j = self.positions.get(d.i)

        if j is None:   # base of spine

            rest = self.transform(d.body)
            if unifies(d.head, self.x):
                return D_rso(d.head, D_o(d)(frozen(d.head), *rest), D_base(slash(d.head, d.head)))

            else:
                if self._is_useful_other(d.head):
                    return D_ro(d.head, D_o(d)(frozen(d.head), *rest))
                else:
                    return D_o(d)(d.head, *rest)

        else:

            dd = self.transform(d.body[j])
            left = self.transform(d.body[:j])
            right = self.transform(d.body[j+1:])

            if Derivation.base(dd):
                o = dd

                if unifies(o, self.x):
                    s = D_base(slash(o, o))
                    name = getx(o)
                    return D_rso(d.head, o, D_ss(d)(slash(d.head, name), *left, s, *right))

                else:
                    o = dd
                    # slash base case; this is the bottommost element of Xs along the spine.
                    if unifies(d.head, self.x):
                        return D_rso(d.head, D_oo(d)(frozen(d.head), *left, o, *right), D_base(slash(d.head, d.head)))
                    else:
                        if self._is_useful_other(d.head):
                            return D_ro(d.head, D_oo(d)(frozen(d.head), *left, o, *right))
                        else:
                            return D_oo(d)(d.head, *left, o, *right)

            elif len(dd.body) == 1:   # frozen

                # XXX: The condtion above might not be a perfect test anymore
                # because of the special handling for useless others - need to
                # double check...this worry might be ruled out by other factors

                [o] = dd.body
                assert o.head.fn == self.other_fn

                # slash base case; this is the bottommost element of Xs along the spine.
                if unifies(d.head, self.x):
                    return D_rso(d.head, D_oo(frozen(d.head), *left, o, *right), D_base(slash(d.head, d.head)))
                else:
                    if self._is_useful_other(d.head):
                        return D_ro(d.head, D_oo(d)(frozen(d.head), *left, o, *right))
                    else:
                        return D_oo(d)(d.head, *left, o, *right)

            else:
                [o, s] = dd.body
                name = getx(o)
                return D_rso(d.head, o, D_ss(d)(slash(d.head, name), *left, s, *right))
