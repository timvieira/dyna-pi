"""
Implements the type analysis with the abstract forward chaining algorithm.
"""

# TODO: anywhere that we encounter an `any` type we can create a free and a
# bound variant


from arsenal import colors
from itertools import combinations

from dyna import (
    pp as _pp, PrettyPrinter, Boolean, Rule, Program, TransformedProgram, vars, fresh, Term, same, unify, Subst, Var,
    MostGeneralSet, snap
)
from dyna.analyze.rewrites import Rewrites


DEBUG = 0

def debug(level=None):   # pragma: no cover
    global DEBUG
    if level is not None:
        from dyna.analyze import rewrites
        DEBUG = level
        rewrites.DEBUG = level
    return debug
_debug = debug


#_______________________________________________________________________________
# Booleanization / type program preprocessing

def add_free_constraints(r):
    assert isinstance(r, Rule), r
    #r = deref(r)
    return Rule(r.head, *r.body, *[Term('$free', v) for v in vars(r.head) - vars(r.body)])

def remove_constants(p, r):
    assert isinstance(r, Rule), r
    return Rule(r.head, *[b for b in r.body if not p.is_const(b)])

def to_type_program(p):
    q = TransformedProgram('booleanize', p, [
        # create $free(X) constraints for each non-range-restricted variable X in the rule.
        remove_constants(p, add_free_constraints(r))
        for r in p
    ])
    q.semiring = Boolean
    return q

def truncate_term(x, D):
    """
    Return a term that covers `x` if we exceed a representational depth limit.
    """
    x = snap(x)
    if D <= 0:
        return Var('$Trunc')   # new variable
    elif isinstance(x, Var):   # must be free because we snapped
        return x
    elif isinstance(x, Term):
        return x.__class__(x.fn, *[truncate_term(y, D-1) for y in x.args])
    else:
        return x

#_______________________________________________________________________________
#

class TypeAnalyzer:
    """
    Type analyzer that uses abstract forward chaining with a constraint
    propagation system and relaxation steps.
    """

    # XXX: insts are an experimental feature
    def __init__(self, program, input_type, rewrites, max_depth=5, use_insts=True, verbosity=0, basic=True):
        if isinstance(input_type, str): input_type = Program(input_type)
        if isinstance(rewrites, str): rewrites = Rewrites(rewrites)

        # To run the program in the input_type, we concatenate them.
        self._program = program
        self._input_type = input_type

        # Apply booleanization transform
        self.program = to_type_program(program + input_type)
        self.inputs = (
            (input_type.inputs or Program([]))      # user type parameters
            + Program('$free(_). $bound(_).')       # "builtin" type parameters
        )
        self.outputs = program.outputs
        self.program.set_input_types(self.inputs)
        self.program.set_output_types(self.outputs)

        # configuration options
        self.use_insts = use_insts
        self.max_depth = max_depth
        self.rewrites = rewrites

        self._verbosity = verbosity

        # As usual in forward chaining, we initialize the chart to empty.
        self.chart = self.program.spawn([])

        if basic:
            self._run_basic()
        else:
            self._run_generalizing()

    def __repr__(self):

        class Foo:
            def __init__(self, x):
                self.x = x
            def __repr__(self):
                return self.x

        # Color $free, $bound, and $any variables differently.
        lines = []
        for x in self.chart.sort():

            pr = PrettyPrinter()

            s = Subst()
            for y in x.body:
                if y.fn == '$free':
                    s[y.args[0]] = Foo(colors.dark.white % f'-{pr(y.args[0])}')
                if y.fn == '$bound':
                    s[y.args[0]] = Foo(colors.dark.blue % f'+{pr(y.args[0])}')
            for y in vars(x) - vars(x.body):
                s[y] = Foo(colors.light.red % f'±{pr(y)}')

            z = Rule(s(x.head), *[y for y in x.body if y.fn not in {'$bound', '$free'}])
            lines.append(f'  {z}')

        lines = "\n".join(lines)

        return 'TypeAnalyzer {\n%s\n}' % lines

    @property
    def DEBUG(self):
        return max(self._verbosity, DEBUG)

    def _run_basic(self):
        "Semi-naive bottom-up evaluation"
        # initialize the agenda (= [full] step on the empty chart)
        agenda = list(self.step())
        _chart = MostGeneralSet(agenda, self.rewrites.covers)
        self.chart = self.program.spawn(_chart.xs)
        while agenda:
            driver = fresh(agenda.pop(0))
            if self.DEBUG > 0: print(colors.light.yellow % "pop", _pp(driver, color=False))
            # drive the rule (we don't need to linearize the body in this case
            # because because the boolean semiring is idempotent)
            for r in self.program:
                for k in range(len(r.body)):
                    # better to have an outer loop over change to improve the number of "prefix firings"
                    for _ in unify(r.body[k], driver.head):
                        for constraints in self.chart.join(*r.body[:k], *r.body[k+1:]):
                            if self.DEBUG > 0: print(colors.dark.magenta % '  ', _pp(r, color=False))
                            for x in self._relax(Rule(r.head, *constraints, *driver.body)):
                                x = fresh(x)
                                if _chart.add(x):    # duplicate
                                    if self.DEBUG > 1: print(colors.dark.yellow % '      duplicate', _pp(x, color=False))
                                else:
                                    if self.DEBUG > 0: print(colors.light.yellow % '      push: ', _pp(x, color=False))
                                    agenda.append(x)
                                    self.chart = self.program.spawn(_chart.xs)
        return self

    def _run_generalizing(self):
        "Naive bottom-up evaluation"
        if self.DEBUG > 0: print(colors.light.magenta % '\n\nIteration:', 0)
        if self.DEBUG > 0: print(colors.light.magenta % 'Chart', self.chart)
        # run forward chaining
        iteration = 0
        while True:
            iteration += 1
            if self.DEBUG > 0: print(colors.light.magenta % '\n\nIteration:', iteration)
            new = self.generalize(self.step())
            if self.DEBUG > 0:
                print(colors.light.magenta % 'Chart (comparison)')
                new.compare(self.chart)
            if new.same(self.chart): break
            self.chart = new
        self.chart = self.chart.sort()
        return self

    def generalize(self, new):
        """
        Make `new` chart disjoint by replacing overlapping pairs of simple types
        with their anti-unifier
        """
        if new is None: new = self.chart
        return self.rewrites.disjoin(new)

    def step(self):
        "Expand the program rules against the chart, returns a Program."
        return self.rewrites.dedup(self.relax(self.program.step(self.chart)))

    def relax(self, S):
        return self.program.spawn([t for s in S for t in self._relax(s)])

    def _relax(self, r):
        _r = r
        r = self.rewrites(r, USE_INSTS=self.use_insts)
        if r is None: return
        # Relax tall terms
        h = truncate_term(r.head, self.max_depth)
        if self.DEBUG > 0 and not same(r.head, h):
            print(colors.red % f'[truncate]     {r.head}')
            print(colors.red % f'[truncate]  -> {h}')
        # Drop any constraint that mentions local variables.
        head_vars = vars(h)
        s = Rule(h, *{x for x in r.body if vars(x) <= head_vars and vars(x)})
        if self.DEBUG > 1:
            print(colors.yellow % '      init: ', _pp(_r, color=False))
            print(colors.yellow % '      prop: ', _pp(r, color=False))
            print(colors.yellow % '      relax:', _pp(s, color=False))

        yield s

    #___________________________________________________________________________
    #

    def intersect(self, Q):
        "Intersect the chart's simple types with q's simple types."
        if isinstance(Q, str): Q = Program(Q)
        assert isinstance(Q, Program), Q
        T = []
        for r in Q:
            for ts in self.chart[r.head * r.body]:
                for t in self._relax(fresh(Rule(r.head, *ts))):
                    T.append(fresh(t))
        return self.rewrites.dedup(self.program.spawn(T))

    def is_disjoint(self, **kwargs):
        "Check pairwise disjointness of types in chart"
        return not any(True for r,s,t in self.find_overlap(**kwargs))

    def find_overlap(self, verbose=False):
        "Check pairwise disjointness of types in chart"
        for s,t in combinations(self.chart, 2):
            r = self.rewrites.intersect(s, t)
            if r is not None:   # pragma: no cover
                if verbose:
                    print('\noverlapping types:')
                    print(s)
                    print(t)
                    print('overlap=>', r)
                yield r, s, t

#    def show_expand(self):
#        for r_ in self._program:
#            print(colors.render(colors.magenta % f'% {r_}'))
#            for h, _, r in self.expand_r(r_):
#                print(f'  {r}  {colors.dark.white % ("% " + str(set(h.body) or dict()))}')

    def assert_equal(self, other):
        self.chart.assert_equal(other)
        return self

    def runtime(self, rs=None, **kwargs):
        from dyna.analyze.runtime import Runtime
        return Runtime(self, **kwargs)(self.program if rs is None else rs)

    def show_runtime(self, **kwargs):
        from dyna.analyze.runtime import Runtime
        R = Runtime(self, **kwargs)
        for r in self._program:
            print(colors.light.magenta % _pp(r, color=False))
            print(R(r))

    def size(self):
        from dyna.analyze.runtime import stype_bound
        return sum(stype_bound(self, t, frozenset(), t.body) for t in self.chart)

    def show_size(self, full=False):
        from arsenal.maths.combinatorics import powerset
        from dyna.analyze.runtime import type_bound, Simplify
        for s in self.chart:
            print()
            print(colors.light.magenta % _pp(s, color=False))
            if full:
                for v in powerset(vars(s)):
                    vv = set(v) or {}
                    bound = Simplify(type_bound(self, s, v))
                    print(f'  {str(vv):>10}  {bound}')
            else:
                bound = Simplify(type_bound(self, s, set()))
                print(f'  {bound}')
