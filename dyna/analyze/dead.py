"""
Dead rule elimination
"""

from dyna import TransformedProgram, Program, Rule
from dyna.term import fresh, Product, DisjointEstimate
from dyna.util.graphs import Hypergraph


#from arsenal import timers
#T = timers()


def prune_very_fast(program):
    #with T['fast']: fast_result = _prune_fast(program)
    #with T['very fast']: very_fast_result = _hg_prune_very_fast(program)
    #with T['very fast prog']: very_fast_result = _prog_prune_very_fast(program)
    return _hg_prune_very_fast(program)


def prune_fast(program):
    #with T['fast']: fast_result = _prune_fast(program)
    #with T['very fast hg']: very_fast_result = _hg_prune_very_fast(program)
    #with T['very fast prog']: very_fast_result = _prog_prune_very_fast(program)
    #with T['slow']: slow_result = program.prune(specialize=False, max_depth=1)
    #with T['slow-specialize']: slow_result = program.prune(max_depth=1)
    #have_hg.assert_equal(want)
    #have_trans.assert_equal(want)
    #T.compare()
    #return _hg_prune_very_fast(program)
    return _prune_fast(program)


# TODO: we should be able to use dyna programs in place of the hypergraph class.
# The algorithm below is equivalent to the prune_very_fast method except that it
# is 60x slower due to overhead in working the programs.  I need to figure out
# why that's the case.
#def _prog_prune_very_fast(program):
#
#    def coarsen(x):
#        if program.is_const(x): return True
#        if program.is_builtin(x): return True
#        return Term(x.fn)
#
#    rs = []
#    for r in program:
#        rs.append(Rule(coarsen(r.head), *tuple(coarsen(b) for b in r.body)))
#    for r in program.inputs:
#        rs.append(Rule(coarsen(r.head)))
#
#    c = Program(rs, semiring=Boolean)
#    c = c + useful(c, output_type=Program(Rule(coarsen(r.head)) for r in program.outputs))
#
#    sol = c()
#
#    def good(x):
#        x = coarsen(x)
#        if x is True: return True
#        return any(sol.lookup_vals(Term('$useful', x)))
#        #return any(sol.lookup_vals(x))
#
#    active_rules = [
#        r
#        for r in program
#        if good(r.head) and all(good(b) for b in r.body)
#    ]
#
#    if len(program) == len(active_rules):
#        return program
#    else:
#        return TransformedProgram('prune-very-fast', program, active_rules)


def _hg_prune_very_fast(program):
    "Prune based on dependencies among the outermost functors."

    assert program.inputs is not None and program.outputs is not None

    inputs = {x.fn for x in program.inputs.just_heads()}
    outputs = {x.fn for x in program.outputs.just_heads()}

    E = [(r.head.fn, i, tuple(b.fn for b in r.body if not program.is_const(b) and not program.is_builtin(b)))
         for i, r in enumerate(program)]

    g = Hypergraph()
    for h,i,bs in E:
        g.add_edge(h,i,*bs)

    T = g.reachability(inputs, outputs)

    active_rules = []
    for (h,_,bs), r in zip(E, program):
        if (h in T) and all((b in T) for b in bs):
            active_rules.append(r)

    if len(program) == len(active_rules):
        return program
    else:
        return TransformedProgram('prune-very-fast', program, active_rules)


# TODO: unify with `dyna.analysis.CoarseGraph`
class ProgramCoarsening:

    def __init__(self, p):
        self.parent = p

        nodes = DisjointEstimate()
        for x in p.inputs.just_heads():
            nodes.add(x)
        for x, *ys in p:
            nodes.add(x)
            for y in ys:
                if p.is_const(y) or p.is_builtin(y): continue
                nodes.add(y)
        self.nodes = nodes

        # coarse-grained hypergraph
        g = Hypergraph()
        for x in p.inputs.just_heads():
            for [i] in self.f(x):
                g.add_edge(i, None)
        for r in p:
            for [xx] in self.f(r.head):
                for yy in self.f(*r.body):
                    g.add_edge(xx, None, *yy)

        # the useful coarse-grained items
        inputs = {i for x in p.inputs.just_heads() for [i] in self.f(x)}
        outputs = {i for x in p.outputs.just_heads() for [i] in self.f(x)}
        self._useful = g.reachability(inputs, outputs)

    def useful(self, x):
        for vs in self._f(x):
            if all((v in self._useful) for v in vs):
                yield vs

    def _f(self, x):
        assert not isinstance(x, (tuple, list, Product)), x
        if self.parent.is_const(x) or self.parent.is_builtin(x):
            yield ()
        else:
            for v in self.nodes.find_all(x):   # uses integer ids (slightly faster, but harder to debug)
                yield (v,)

    def f(self, *xs):
        if len(xs) == 0: yield ()
        else:
            [x,*xs] = xs
            for v in self._f(x):
                for vs in self.f(*xs):
                    yield (*v, *vs)


def _prune_fast(program):
    "Prune based on superficial items in the program"

    #if program.inputs is None or program.outputs is None: return program
    assert program.inputs is not None and program.outputs is not None

    self = program

#    def lookup(x):
#        assert isinstance(x, Term)
#        return list(nodes.roots(x))

#    nodes = program.coarse_nodes()
#    g = program.coarse_hypergraph()
#    roots = nodes.roots

#    inputs = {i for x in program.inputs.just_heads() for i in lookup(x)}
#    outputs = {i for x in program.outputs.just_heads() for i in lookup(x)}

    c = ProgramCoarsening(program)

    #E = {(e.head, frozenset(e.body)) for x in g.incoming for e in g.incoming[x]}
#    T = g.reachability(inputs, outputs)

    def good(x):
        return any(True for _ in c.useful(x))

    active_rules = [r for r in program if good(r.head) and all(good(b) for b in r.body)]

    if len(program) == len(active_rules):
        return program
    else:
        return TransformedProgram('prune-fast', program, active_rules)


# TODO: [2022-11-12 Sat] this can be very slow (e.g., dead.py:test_cky0 takes
# ~12s); it's probably to due to insufficient indexing.
#
# TODO: implement the improved version from the dissertation, that version
# supports general types, much like the new abbreviation transformation.
def _prune_specialize(p, analysis):
    D = DisjointEstimate([r.head for r in analysis])
    S = Program([Rule(x) for x in D])
    # Note: the code below differs from `Program.instantiate` because the head can drive.
    new = [fresh(r) for r in p for _ in S.join(r.head, *r.body)]
    new = TransformedProgram('prune-specialize', p, new)
    return p if new == p else new


def _prune_dead(p, analysis):
    # Note: differs from `Program.instantiate` as the head can drive.
    new = [r for r in p if any(True for _ in analysis.join(r.head, *r.body))]
    if len(p) == len(new):
        return p
    else:
        return TransformedProgram('prune-dead', p, new)
