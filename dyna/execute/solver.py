"""Simple implementation of the Dyna inference algorithm.

The implementation in this module follows Eisner et al (2005).  It does not
support nonground updates or delayed constraints; it throws an exception when
it encounters either.

"""

from arsenal import colors, Integerizer
from arsenal.datastructures.heap import LocatorMaxHeap  # Warning: BucketQueue takes argmin whilst LocatorMaxHeap takes argmax.
from collections import Counter, defaultdict

from dyna.util.bucket_queue import BucketQueue
from dyna import (
    term, NotMatchesConstaint, SolverLimitation, InstFault, unify, fresh,
    is_ground, Term, unifies, snap, syntax
)
from dyna.execute.base import BaseSolver, tupleone, cmps


class Solver(BaseSolver):
    """
    Dyna1 inference which supports ground updates.
    """

    def __init__(self, rules, debug=False, priority=None, AgendaType=LocatorMaxHeap):

        self.chart = Chart()
        self.change = {}
        self.agenda = AgendaType()

        self.debug = debug
        self.priority = priority

        self.intern = Integerizer()

        self.pops = 0
        self.pops1 = 0
        self.pushes = 0

        super().__init__(rules)

        # index from driver (functor-airity) to a sequence of rule id and subgoal pairs.
        self.ix_drivers = defaultdict(list)
        for i, r in enumerate(self.program):
            for k, y in enumerate(r.body):
                if self.program.is_builtin(y) or self.program.is_const(y): continue
                self.ix_drivers[y.fn, y.arity].append((i,k))

    def __repr__(self):
        return f'Solver{"*" if self.agenda else ""} {self.sol()}'

    def update(self, item, Δ):
        if not is_ground(item):
            raise SolverLimitation(f'nonground updates are not supported: {item}')

        self.pushes += 1

        item = self.intern(fresh(item))

        if self.debug: print(f'    {colors.yellow % "push"}: {self.intern[item]} += {Δ}')
        if item not in self.change:
            item = fresh(item)
            self.change[item] = Δ
        else:
            self.change[item] += Δ

        # Roughly FIFO
        if self.priority is None:
            p = -self.pushes
        else:
            p = self.priority(item)
        if p is not None:                # p = None ==> prune update
            self.agenda[item] = p

    def _forward_chaining(self):
        for r in self.program: self.init_rule(r)
        while self.agenda:
            [a, _] = self.agenda.popitem()
            Δ = self.change.pop(a)
            a = self.intern[a]
            self.pops += 1
            # don't propagate if unchanged
            old = self.chart.chart.get(a, self.zero)
            new = old + Δ
            if self.approx_equal(new, old):
                if self.debug: print(f'{colors.light.yellow % "pop"}: {fresh(a)} ... no change')
                continue
            # update the chart with the Δ update
            self.chart[a] = new
            self.pops1 += 1   # pop actually result in propagation
            if self.debug: print(f'{colors.light.yellow % "pop"}: {a} += {Δ}', colors.magenta % f'(old: {old}, new: {new})')
            # ground out rules against the current chart
            for i, s, P in self.drive_rules(a, old, Δ):
                # carefully apply the Δ-update to avoid double counting.
                c = self.one
                for j, z in enumerate(s.body):   # XXX: better to reuse prefix products or binarize
                    if j < i and z == a:
                        c *= old
                    elif i == j:
                        c *= Δ
                    else:
                        c *= P[j]
                self.update(s.head, c)
        return self

    def drive_rules(self, a, old, Δ):
        "Drive rules affected by item `a`."
        for I, k in self.ix_drivers[a.fn, a.arity]:
            r = self.program.rules[I]
            b = r.body[k]
            for _ in unify(a, b):
                if self.debug > 0: print(colors.render(colors.dark.magenta % f'# drive ({k}):  {r}'))
                for P in self.join(r.body, tupleone):
                    if self.debug > 0: print(colors.render(colors.magenta % f'> ground ({k}): {r}'))
                    yield k, r, P

    def lookup_vals(self, q):
        q = snap(q)   # recurse on q.value if bound

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

        else:
            yield from self.chart[q]


class Chart:

    def __init__(self):
        self.chart = {}
        self.index = {}

    def items(self):
        return self.chart.items()

    def __setitem__(self, item, v):
        self._update_index(item)
        self.chart[item] = v

    def __getitem__(self, q):
        "Drive subgoal by matching against the chart."
        yield from self._indexed_lookup(q)

    def _indexed_lookup(self, q):
        fa, m = query_mode(q)       # m is the list of bound variables

        avail = self.index.get(fa)
        if avail is None:
            self.index[fa] = avail = {}

        ix = avail.get(m)
        if ix is None:
            self.index[fa][m] = ix = self._build_index(fa, m)

        k = tuple(q.args[i] for i in m)
        xs = ix.get(k, set())

        for x in xs:
            for _ in unify(x, q):
                yield self.chart[q]

    def _build_index(self, fa, m):
        f,a = fa
        ix = defaultdict(set)
        for x in self.chart:
            if x.fn == f and x.arity == a:
                ix[tuple(x.args[i] for i in m)].add(x)
        return dict(ix)

    # Our policy for creating indexes is not great.  We end up creating a lot of
    # indexes that we only use once (e.g., the init method on CKY looks for all
    # phrases that use a given terminal, which is a useful mode if the grammar
    # changes pretty often, but that's not what happens most of the time).
    #
    #   It's not showing up as a bottleneck in the profiler (I'm running on
    #   papa-cky).
    #
    # It should be possible to determine which indexes we want by static
    # analysis -- it's the same thing that McAllester does.
    def _update_index(self, item):
        if item not in self.chart:
            # only need to update indexes when we get a new item because they
            # only track the support.
            fa = (item.fn, item.arity)
            if fa in self.index:
                for m in self.index[fa]:
                    k = tuple(item.args[i] for i in m)
                    ix = self.index[fa][m]
                    if k not in ix: ix[k] = set()
                    ix[k].add(item)


def query_mode(q):
    return ((q.fn, q.arity),
            tuple(i for i, x in enumerate(q.args)
                  if is_ground(x)
            ))
