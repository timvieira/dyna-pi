"""
Fold-unfold safety measures
"""
import z3
from arsenal import colors

from dyna import Program
#from dyna.analyze.abbreviate import Abbreviate
from dyna.derivations import Derivation, Product
from dyna.program import Define
from dyna.term import fresh, unifies


class measure_safety:
    def __init__(self, m, p, safe):
        assert isinstance(safe, list)
        self.m = m
        self.p = p
        self._safe = safe
        self._id = 0

    def is_safe(self):
        if all(c is True or c is False for c in self._safe):
            return all(self._safe)      # concrete (unit) measures -> no SMT solve needed
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

    def __init__(self, symbolic=True):
        self.measures = {}
        self._var_id = 0
        self.symbolic = symbolic
        # Constructors exposed so each transform's `compute_measure(M)` method
        # can build measures through the Measure context `M` rather than
        # importing them from this module. This keeps the transforms agnostic of
        # the measure representation and decoupled from this module entirely (it
        # imports `dyna`, so a transform reaching back in could risk a cycle).
        self.Interval = Interval
        self.Min = Min
        self.Max = Max

    def new_var(self):
        if not self.symbolic:
            return (1, [])          # concrete unit measure: fast, no symbolic z3 blowup on deep chains
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
        # Cache-miss handler. Each Program builds its own measure against this
        # Measure context via `compute_measure` (transforms derive from their
        # parents; the dispatch lives on the program classes, not here). The
        # reference program's initial measure is pre-cached by `add_ref`, so it
        # never reaches this path.
        return new.compute_measure(self)

    # ----- constructors / shared measures exposed to transform `compute_measure(M)` methods -----
    # These let a transform build its measure through the Measure context `M` instead of
    # importing this module, keeping the transforms decoupled from the measure representation.

    def safety(self, m, p, safe):
        "Construct a measure_safety record."
        return measure_safety(m, p, safe)

    def zero_measure(self, p):
        "An all-zero, unsafe measure for `p` (freshness violations / unknown transforms)."
        return measure_safety([Interval(0, 0)] * len(p), p, safe=[False])

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

    def _freshness_violations(self, parent, defs):
        """For fold/unfold safety: every Define operation in `defs`'s lineage
        must also appear in `parent`'s lineage. Otherwise `defs` is carrying
        a rule (or rules) that `parent` never agreed to — a "sibling Define"
        — and folding/unfolding via that rule silently introduces an equation
        the algebra never checks for consistency with `parent`'s definitions.

        For each foreign Define in `defs`'s lineage, we report a violation
        when any of its new rule heads unifies with any head in `parent`.

        Returns the list of (defs_rule, parent_head) pairs that violate..
        """
        parent_stage_ids = {id(s) for s in parent.lineage()}
        violations = []
        for stage in defs.lineage():
            if not isinstance(stage, Define):
                continue
            if id(stage) in parent_stage_ids:
                continue
            # This Define is in defs's lineage but NOT in parent's. Its new
            # rules are foreign to parent. Flag any whose head clashes.
            for idx in stage._new_ix:
                d_rule = stage.rules[idx]
                for p_rule in parent.rules:
                    if unifies(fresh(d_rule.head), fresh(p_rule.head)):
                        violations.append((d_rule, p_rule.head))
                        break
        return violations

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


def make_smt_measure(p, symbolic=True):
    m = Measure(symbolic=symbolic)
    m.add_ref(p)
    return m
