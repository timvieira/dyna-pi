"""
Dyna inference which supports nonground updates, but no other delayed constraints.
"""

import numpy as np

from arsenal.datastructures.heap import LocatorMaxHeap
from arsenal import colors, Integerizer

from dyna import (
    Program, Boolean, term, SolverLimitation, unify, fresh, Term, unifies,
    canonicalize, snap, covers, intersect, DisjointEstimate, is_ground,
    InstFault
)

from dyna.builtin import NotMatchesConstaint
from dyna.execute.base import BaseSolver, cmps


class Solver(BaseSolver):
    """
    Dyna inference which supports nonground updates.
    """

    def __init__(self, program, debug=False, priority=None, AgendaType=LocatorMaxHeap):
        program = program.linearize()   # so I don't have to worry about double counting diagonals...
        self.program = program

        self.chart = {}
        self.change = {}
        self.agenda = AgendaType()
        self.debug = debug
        self.priority = priority

        self.intern = Integerizer()

        self.pops = 0
        self.pops1 = 0
        self.pushes = 0

        super().__init__(program)

    def __repr__(self):
        return f'Solver{"*" if self.agenda else ""} {self.sol()}'

    def user_query(self, q, **kwargs):
        """
        Answer user query `q`, returns a (mostly consolidated)
        program with += aggregators.
        """
        return super().user_query(q, **kwargs).constant_folding().sort()

    def update(self, item, Δ):

        # I think canonicalize is enough - no need to call fresh;
        # canonicalize will also (conveniently) intern all items (both ground and nonground).
        # I guess that's not useful to this implementation because we mutate the item and,
        # therefore, have to freshen it when we grab it from the chart :-/

        if self.debug: print(f'    push: {item} += {Δ}')

        item = fresh(item)
        item = canonicalize(item)
        item = self.intern(item)

        self.pushes += 1
        if item not in self.change:
            self.change[item] = Δ
        else:
            self.change[item] += Δ

        # Residual-based prioritization isn't generally good.
        #self.agenda[item] = abs(self.change[item])

        # Roughly FIFO
        if self.priority is None:
            p = -self.pushes
        else:
            p = self.priority(item)
        if p is not None:                # p = None ==> prune update
            self.agenda[item] = p

    def __setitem__(self, item, v):
        # TODO: update indexes

        item = canonicalize(item)

#        i = self.ix.get(item)
#        if i is None:
#            self.ix[item] = len(self.ix)
#            self.chart_p.append(Rule(item, v))
#        else:
#            r = self.chart_p[i]
#            [V] = r.body
#            self.chart_p[i] = Rule(r.head, V + v)

        self.chart[item] = v

    def _forward_chaining(self):
        for r in self.program: self.init_rule(r)
        while self.agenda:
            [a, _] = self.agenda.popitem()
            Δ = self.change.pop(a)
            a = self.intern[a]   # note: fresh happens later when we drive
            self.pops += 1
            # don't propagate if unchanged
            old = self.chart.get(a, self.zero)
            new = old + Δ
            if self.approx_equal(new, old):
                if self.debug: print(f'pop: {fresh(a)} ... no change')
                continue
            # update the chart with the Δ update
            self[a] = new
            self.pops1 += 1   # pop actually result in propagation
            if self.debug: print(f'pop: {a} += {Δ}', colors.magenta % f'(old: {old}, new: {new})')
            # ground out rules against the current chart
            for s, v in self.drive_rules(fresh(a), old, Δ):
                self.update(s.head, v)
        return self

    def drive_rules(self, a, old, Δ):
        "Drive rules affected by item `a`."
        for r in self.program:
            for v in self.drive_rule(r, a, old, Δ):
                yield (r, v)

    def drive_rule(self, r, a, old, Δ):
        for i, b in enumerate(r.body):    # TODO: use subgoal rule index
            for _ in unify(a, b):
                bs = list(r.body); bs[i] = Δ   # replace subgoal i with Δ.
                for v in self.join(bs, self.one):
                    yield v * self.program.multiple(r)

    def lookup_vals(self, q):
        """
        Answer query `q` by matching it against the chart,
        returns a stream of bindings to `q` and emits contribs.
        """
        q = snap(q)

        # special handling for constants.
        if self.program.is_const(q):
            yield q
            return

        elif not isinstance(q, Term):
            raise InstFault(f'query mode not supported: {q}')

        elif q.fn == '$not_matches':
            for r in NotMatchesConstaint(*q.fargs).run(self.program):
                if r.is_const():
                    yield self.one
                else:
                    raise InstFault()

        elif q.fn == '=':
            x,y = q.args
            for _ in unify(x,y):
                yield self.one
            return

        elif q.fn in cmps and q.arity == 2:
            x,y = q.args
            x = snap(x)
            y = snap(y)
            if is_ground(x) and is_ground(y):
                if cmps[q.fn](x, y): yield self.one
                return            # failure
            else:
                raise InstFault(f'query mode not supported: {q}')

        elif q.fn == 'is':
            for _ in self.builtins(q):
                yield self.one
            return

        else:
            for x, v in self.chart.items():   # XXX: use indexing!!!
                #assert iswrap(x), x
                x = fresh(x)
                for _ in unify(x, q):
                    yield v
