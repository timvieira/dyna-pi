"""
Fold-unfold safety measures
"""
import z3
from arsenal import colors

from dyna import Program, TransformedProgram
#from dyna.analyze.abbreviate import Abbreviate
from dyna.derivations import Derivation, Product
from dyna.program import Define
from dyna.transform import Fold, Unfold, Slash, LCT


class measure_safety:
    def __init__(self, m, p, safe):
        assert isinstance(safe, list)
        self.m = m
        self.p = p
        self._safe = safe
        self._id = 0

    def is_safe(self):
        s = z3.Solver()
        s.reset()
        s.add(self._safe)
        return s.check() == z3.sat

    def __repr__(self, c='%s'):
        msg = ''

        s = z3.Solver()
        s.add(self._safe)
        if s.check() == z3.sat:
            ms = str(s.model()).replace("\n","")
            marker = f'{colors.mark(True)} {ms}'
        else:
            marker = colors.mark(False)

        lines = [c % f'measure_safety(safe={marker}, {{']
        for i in range(len(self.p)):
            lines.append(colors.render(c % f'  {i}: {self.m[i]}: {self.p.rules[i]}'))
        lines.append((c % '})') + colors.render(colors.dark.white % msg))
        return '\n'.join(lines)

    def align(self, p):
        if p is self.p: return self
        m = [None]*len(self.p)
        for i,j in p.align(self.p):  # Important! align the programs
            m[i] = self.m[j]
        return measure_safety(m=m, p=p, safe=self._safe)

    def derivation_measure(self, d):
        "Use clause measures to bound the size of the deriviation `d` in the reference program"
        if isinstance(d, (Product, tuple, list)):
            return Interval.sum(self.derivation_measure(y) for y in d)
        elif Derivation.base(d):
            return Interval.zero
        else:
            assert d.p is None or d.p == self.p
            return self.m[d.i] + self.derivation_measure(d.body)


class Measure:

    def __init__(self):
        self.measures = {}
        self._var_id = 0

    def new_var(self):
        x = f'V{self._var_id}'
        self._var_id += 1
        x = z3.Int(x)
        return (x, [x > 0])

    def add_ref(self, p):
        assert isinstance(p, Program)
        m = []; s = []
        for _ in range(len(p)):
            x, x_s = self.new_var()
            s.extend(x_s)
            m.append(Interval(x,x))
        self[p] = m = measure_safety(m, p, s)
        return m

    def __setitem__(self, p, m):
        self.measures[self._key(p)] = m

    def _key(self, p): return p

    def __call__(self, new):
        assert isinstance(new, Program), [type(new), new]
        key = self._key(new)
        m = self.measures.get(key)
        if m is None:
            self[key] = m = self.compute(new)
        return m.align(new)

    # We use the size in the root program it will be the tightest bound; the
    # other measures would just be trying to estimate it anyways!
    def min_size(self, xs):
        if isinstance(xs, tuple):
            return sum(self.min_size(x) for x in xs)
        elif Program.is_const(xs) or Program.is_builtin(xs):
            return 0
        else:
            return 1

    def safe(self, x):
        return self(x).is_safe()

    def compute(self, new):
        if isinstance(new, Unfold):
            return self._measure_unfold(new)
        elif isinstance(new, Fold):
            return self._measure_fold(new)
        elif isinstance(new, TransformedProgram) and new.name == 'fresh':  # pragma: no cover
            return self(new.parent)
        elif isinstance(new, Define):
            return self._measure_define(new)
        elif isinstance(new, Slash):
            return self._measure_slash(new)
        elif isinstance(new, LCT):
            return self._measure_lct(new)
#        elif isinstance(new, Abbreviate):
#            return self._measure_abbreviate(new)
        else:
#            raise NotImplementedError(f'{type(new)} {new}')
            assert not isinstance(new, TransformedProgram), [new.name, type(new)]
            return measure_safety([Interval(0,0)]*len(new), new, safe=[False])
#            raise KeyError((type(new).__name__, new))

    # XXX: EXPERIMENTAL
    def _measure_define(self, new):
        n = len(new.defs)
        assert len(new.rules[-n:]) == n
        m_parent = self(new.parent)
        safety = list(m_parent._safe)   # copy, because we will append
        m_new = [None] * len(new)
        for i in new._old_ix:
            m_new[i] = m_parent.m[i]   # copy
        for i in new._new_ix:
            x, x_s = self.new_var()
            safety.extend(x_s)
            m_new[i] = Interval(x, x)
        return measure_safety(m_new, new, safety)

#    def _measure_abbreviate(self, new):
#        m_parent = self(new.parent)
#        safety = list(m_parent._safe)   # copy, because we will append
#        m_new = [None] * len(new)
#        for i, r in enumerate(new):
#            if r._orig_rule_index is None:
#                m_new[i] = Interval(0,0)
#            else:
#                m_new[i] = m_parent.m[r._orig_rule_index]
#        return measure_safety(m_new, new, safety)

    # XXX: incorrect
#    def _measure_reversible_fold(self, new):
#        assert isinstance(new, Fold) and new.safe_by_rev
#        m_new = [None]*len(new)
#        m_parent = self(new.parent)
#        diffs = [m_parent.m[P] for P in new.S]
#        m_r = Interval(Min([x.lo for x in diffs]), Max([x.hi for x in diffs]))
#        for N, r in enumerate(new):
#            if N == new.i:
#                m_new[N] = m_r
#            else:
#                m_new[N] = m_parent.m[new.parent.rules.index(r)]
#        # a reversible fold is safe as long as its parent is safe.
#        safe = list(m_parent._safe)
#        return measure_safety(m_new, new, safe)

    def _measure_fold(self, new):
        assert isinstance(new, Fold) #and new.undo == new.parent
        assert new.partially_safe
        #if not new.partially_safe: return self._measure_reversible_fold(new)
        return self._measure_generalized_fold(new)

    def _measure_generalized_fold(self, new):
        m_new = [None]*len(new)
        m_parent = self(new.parent); m_defs = self(new.defs)
        diffs = [m_parent.m[P] - m_defs.m[D] for P,D in new.par2def.items()]
        m_r = Interval(Min([x.lo for x in diffs]), Max([x.hi for x in diffs]))
        for N, r in enumerate(new):
            if N == new.i:
                m_new[N] = m_r
            else:
                m_new[N] = m_parent.m[new.parent.rules.index(r)]
        # Check the safety conditions for generalized fold.
        safe = m_parent._safe + m_defs._safe
        for (D,P) in new.def2par.items():
            extra = self.min_size(new.bookkeeping[P].left) + self.min_size(new.bookkeeping[P].right)
            safe.append(
                (m_parent.m[P] - m_defs.m[D]).lo + extra > 0
            )
        return measure_safety(m_new, new, safe)

    def _measure_unfold(self, new):
        assert isinstance(new, Unfold) #and new.undo == new.parent

        m_new = [None]*len(new)
        m_parent = self(new.parent); m_defs = self(new.defs)

        for N, r in enumerate(new):
            if N in new.new2def:
                m_new[N] = m_parent.m[new.i] + m_defs.m[new.new2def[N]]
            else:
                m_new[N] = m_parent.m[new.parent.rules.index(r)]

        # Check the safety conditions for generalized unfold.
        P = new.i
        safe = m_parent._safe + m_defs._safe
        for (_,D) in new.new2def.items():
            # don't count the size of the subgoal that we replaced in the unfold action
            extra = self.min_size(new.parent.rules[P].body[:new.j]) + self.min_size(new.parent.rules[P].body[new.j+1:])
            safe.append(
                    (m_parent.m[P] + m_defs.m[D]).lo + extra > 0
            )
        return measure_safety(m_new, new, safe)

    def _measure_slash(self, new):
        assert isinstance(new, Slash)

        m_par = self(new.parent)
        m = [None] * len(new)

        # Each rule of the new program falls into one of 6 categories: ss, oo,
        # o, rso, ro, base.

        # Each rule in (ss ∪ oo ∪ o) inherits its clause measure from the rule
        # in the parent that gave rise to it.
        for i, r in new.ss.items():  m[r._index] = m_par.m[i]
        for i, r in new.oo.items():  m[r._index] = m_par.m[i]
        for i, r in new.o.items():   m[r._index] = m_par.m[i]

        # Each of the remaining rules (those in {base} ∪ rso ∪ ro), have a
        # measure of zero.
        if 1:                        m[new.base._index] = Interval(0,0)
        for r in new.rso.values():   m[r._index] = Interval(0,0)
        for r in new.ro.values():    m[r._index] = Interval(0,0)

        return measure_safety(m, new, m_par._safe)

    def _measure_lct(self, new):
        assert isinstance(new, LCT)

        m_par = self(new.parent)
        m = [None] * len(new)

        # Each rule of the new program falls into one of 6 categories: ss, oo,
        # o, rso, ro, base.

        # Each rule in (ss ∪ oo ∪ o) inherits its clause measure from the rule
        # in the parent that gave rise to it.
        for i, r in new.ss.items():  m[r._index] = m_par.m[i]
        for i, r in new.oo.items():  m[r._index] = m_par.m[i]
        for i, r in new.o.items():   m[r._index] = m_par.m[i]

        # Each of the remaining rules (those in {base} ∪ rso ∪ ro), have a
        # measure of zero.
        if 1:                        m[new.base._index] = Interval(0,0)
        for r in new.rso.values():   m[r._index] = Interval(0,0)
        for r in new.ro.values():    m[r._index] = Interval(0,0)

        return measure_safety(m, new, m_par._safe)


# This is a crude estimator of the smallest derivation measure - it's just
# the number of non-size-zero items.
#class SmallestDerivationEstimator:
#    def __init__(self, measure, T):
#        self.T = T
#        self.p = measure.p
#        self.m = measure.m
#        self.measure = measure
#
#    def __call__(self, xs):
#        raise NotImplementedError()
#
#    def __repr__(self):
#        return 'SimpleDerivationSizeEstimator()'
#
#
#class FastSDE(SmallestDerivationEstimator):
#
#    def __call__(self, xs):
#        if isinstance(xs, tuple):
#            return self.T.sum([self(x) for x in xs])
#        elif self.p.is_const(xs) or self.p.is_builtin(xs):
#            return 0
#        else:
#            return 1
#
#
## TODO: I'm running into issues with inefficiency in the system below.
#from arsenal import Integerizer
#names = Integerizer()
#class AccurateSDE(SmallestDerivationEstimator):
#    def __init__(self, measure, T):
#        super().__init__(measure, T)
#
#        # TODO: Use graph from type analysis instead (may be the default for
#        # `coarse_hypergraph` in the future).  The stratified counters wouldn't
#        # need to use the same coarse node representation, but it would probably
#        # be best if they did. If a rule gives rise to mutliple types for the
#        # head, then the stratified counters would have multiple nonzero
#        # elements.  In such a case, it is probably preferrable to partition by
#        # the disjoint types (like pruning/specialization).
#
#        # TODO: I am concerned that the smallest derivation algorithms might not
#        # return a proper lower bound because it is not working its way down
#        # from the top (i.e., an infinite-size upper bound), rather. it is
#        # working up from the bottom (i.e., starting by assuming min-size is
#        # zero and working its way up).  One inconvenience is that I can't stop
#        # minimal fixpoint early and get an upper bound as the output.
#
#        assert isinstance(measure, measure_safety), measure
#
#        p = measure.p
#        self.m = measure.m
#
#        h = p.coarse_hypergraph()
#        nodes = p.coarse_nodes()
#
#        if any(isinstance(v.lo, z3.ArithRef) or isinstance(v.hi, z3.ArithRef)
#               for v in self.m):
#
#            # when using smt, can we can define the min-size derivations with
#            # constraints
#            #
#            # minsize[x] <= measure[r] + minsize[y1] + ... + minsize[yK]
#            #
#            i = names(p)
#            chart = {x: MVar(f'minsize_{i}({x})') for x in h.nodes}
#            for x in h.nodes:
#                for e in h[x]:
#                    if e.weight is not None:
#                        chart[x] = Min([
#                            chart[x],
#                            self.m[e.weight].lo + T.sum([chart[y] for y in e.body])
#                        ])
#                    else:
#                        # Special handling of inputs
#                        assert len(e.body) == 0
#                        chart[x] = Min([
#                            chart[x],
#                            T.zero
#                        ])
#            self.chart = chart
#
#        else:
#            old = {x: T.top for x in h.nodes}
##            for _ in range(len(p)+1):
#            while True:
#                new = {x: T.top for x in h.nodes}
#                for x in h.nodes:
#                    for e in h[x]:
#                        if e.weight is not None:
#                            new[x] = Min([
#                                new[x],
#                                self.m[e.weight].lo + T.sum([old[y] for y in e.body])
#                            ])
#                        else:
#                            # Special handling of inputs
#                            assert len(e.body) == 0
#                            new[x] = Min([
#                                new[x],
#                                T.zero
#                            ])
#                if old == new: break
#                old = new
#            self.chart = old
#
#        self.T = T
#        self.nodes = nodes
#        self.p = p
#
#    def __call__(self, xs):
#        if isinstance(xs, tuple):
#            return self.T.sum([self(x) for x in xs])
#        elif self.p.is_const(xs) or self.p.is_builtin(xs):
#            return self.T.zero
#        else:
#            return self.chart[self.nodes.root(xs)]
#
#    def __repr__(self):
#        return repr(self.chart)


def Min(vs):
    "Return minimum of a vector; error if empty"
    if not any(isinstance(v, z3.ArithRef) for v in vs): return min(vs)
    m = vs[0]
    for v in vs[1:]:
        m = z3.If(v < m, v, m)
    return m


def Max(vs):
    "Return maximum of a vector; error if empty"
    if not any(isinstance(v, z3.ArithRef) for v in vs): return max(vs)
    m = vs[0]
    for v in vs[1:]:
        m = z3.If(v > m, v, m)
    return m


And = z3.And
#def And(x, y):
#    if isinstance(x, z3.BoolRef) or isinstance(y, z3.BoolRef):
#        return z3.And(x, y)
#    else:
#        return x & y


class Interval:

    def __init__(self, lo, hi):
        self.lo = lo
        self.hi = hi

    def __repr__(self):
        if self.lo == self.hi: return f'[{self.lo}]'
        return f'[{self.lo},{self.hi}]'

    def __hash__(self):
        raise NotImplementedError()

    def __eq__(self, other):
        return self.lo == other.lo and self.hi == other.hi

    def __add__(self, other):
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other):
        return Interval(self.lo - other.hi, self.hi - other.lo)

#    def __or__(self, other):
#        return Interval(min(self.lo, other.lo), max(self.hi, other.hi))

    @classmethod
    def sum(cls, xs):
        y = cls.zero
        for x in xs:
            y += x
        return y


Interval.zero = Interval(0, 0)


def make_smt_measure(p):
    m = Measure()
    m.add_ref(p)
    return m
