import numpy as np
import warnings
from arsenal import colors

from dyna import Program, Rule, fresh, vars, Term, unify, Subst
from dyna.analyze import TypeAnalyzer

from dyna.pretty import PrettyPrinter

from functools import lru_cache
cache = lru_cache(maxsize=None)   # for python 3.8, otherwise use functools.cache


DEBUG = 0

import sympy
#sympy.init_printing(use_unicode=True)

_syms = {}
def Symbol(x):
    if x not in _syms:
        assert isinstance(x, str), x
        _syms[x] = sympy.Symbol(x, positive=True, integer=True)
    return _syms[x]
def Simplify(x):
    if isinstance(x, Param): x = x.x
    return sympy.factor(sympy.expand(x))
#def Pretty(x):
#    #return sympy.pretty(x)
#    return x


class Param:
    "Wrapper to facilitate operator overloading"
    def __init__(self, x):
        assert not isinstance(x, Param), type(x)
        self.x = x
    def __add__(self, y):
        return Param(self.x + y.x)
    def __radd__(self, y):
        return self + Param(y)
    def __mul__(self, y):
        return Param(self.x * y.x)
    def min(self, y):
        return Param(sympy.Min(self.x, y.x))
    def __xor__(self, y):
        return self.min(y)
    def __repr__(self):
        return f'{self.x}'


def type_bound(S, stype, V):
    assert isinstance(S, TypeAnalyzer) and isinstance(stype, Rule)
    assert issubset(V, vars(stype))
    q = Program([fresh(stype)])
    ts = []
    T = S.intersect(q)
    for t in T:
        for _ in unify(t.head, stype.head):
            ts.append(stype_bound(S, t, frozenset(V), t.body))
    return sum(ts)


# Every simple type has an item as its head and constraints as its body
def stype_bound(S, s, V0, remaining0):
    return SizeBounds(S, s)._stype_bound(V = frozenset(V0),
                                         remaining = frozenset(remaining0))


class SizeBounds:
    def __init__(self, S: 'type analysis', s: 'simple type'):
        assert isinstance(s, Rule), type(s)   # s simple type
        self.S = S
        self.s = s

    def lookup_bounds(self, c, V):
        assert isinstance(c, Term) and isinstance(V, (set, frozenset))

        fully_bound = issubset(vars(c), V)

        if fully_bound:             # cost=1 if all vars are bound
            yield Param(1)
            return

        # TODO: consult a table of these facts including any user declarations
        # |` type | vars `| <= polynomial

        # enumerating lessthan is too expensive! (it's essentially an invalid
        # mode, so we don't bother enumerating plans that use it.)
        if self.S.program.is_builtin(c): return

        yield Param(Symbol(c.fn))

    @cache
    def _stype_bound(self, V, remaining):
        "Optimize the covering of delayed constraints `cs`."
        s = self.s

        if DEBUG: indent = '    '*(len(s.body) - len(remaining))

        # Base case: no more constraints to consider: bound = 1.
        if len(remaining) == 0:
            #assert vars(s.head).issubset(V), f'subgoal must come to ground: {s}, {V}'
            if issubset(frozenset(vars(s.head)), V):
                return Param(1)
            else:
                # variables which do not come to ground are assumed to range over an
                # infinite domain (i.e., the Herbrand universe).
                #print(f'subgoal must come to ground: {s}, {V}')
                return Param(np.inf)

        best = Param(np.inf)
        for c in remaining:

            for cost in self.lookup_bounds(c, V):

                if DEBUG:
                    pp = PrettyPrinter()
                    print(indent, pp(c), pp(vars(c)), pp(V), '==>', cost)

                best ^= cost * self._stype_bound(
                    V = frozenset(V) | frozenset(vars(c)),   # we assume that all variables are brought to ground by the mode
                    remaining = remaining - {c},             # no use in running this constraint again
                )

        if DEBUG: print(indent, 'cost-to-go', best)
        return best


def issubset(a, b):
    a = set(a); b = set(b)
    return a.issubset(b)


class Runtime:

    def __init__(self, S, fast_mode=False):
        self.S = S
        self.fast_mode = fast_mode

    def __call__(self, r):
        if isinstance(r, (list, Program)):
            return sum([self(s) for s in r])
        else:
            assert isinstance(r, Rule), r
            return self._suffixtime(frozenset(r.body), frozenset([]), frozenset())

    @cache
    def _suffixtime(self, suffix, C, V):
        """
        Recursive function tells us the optimal "suffix runtime" for a rule when
        given an unordered set of subgoals have already been grounded \prefixset.
        Let $\mathcal{C}$ be the union of the constraints for subgoals in prefix.}
        """

        best = Param(np.inf)
        S = self.S

        if DEBUG:
            indent = '    '*len(suffix)
            m = lambda x: colors.render(colors.magenta % x)

        # Optimize over the choice of next subgoal from the set of remaining subgoals

        if DEBUG:
            print(indent, m('suffix:'), suffix or {},
                  m('bound vars:'), set(V) or {},
                  m('context:'), C or {})

        if len(suffix) == 0:
            if DEBUG: print(indent, colors.yellow % 'cost:', 1)
            return Param(1)

        for passenger in (
                # XXX: hack to make things run fast; avoid exponential-time search over subsets
                list(suffix)[:1] if self.fast_mode else suffix
        ):
            # sum over simple types for the chosen subgoal $\est{b}

            t = Param(0)

            if DEBUG: print(indent, colors.yellow % 'pick subgoal:', passenger)

            for (subst1, passenger_stype) in self.lookup(passenger, Subst()):

                s1 = S.rewrites(subst1(Rule(passenger, *passenger_stype.body, *C)))

                if DEBUG:
                    print(indent+'  ', m('simple type:'), passenger_stype)
                    print(indent+'  ', m('simplified:'), s1)

                if s1 is None: continue

                C2 = frozenset(s1.body)   # latest constraint closure

                # upper bound on cardinality of moded query of the current simple type
                # The upper bound $\Sp$ is itself a min as we have seen before.

                q = stype_bound(S, passenger_stype, V0 = V, remaining0 = passenger_stype.body)

#                ppp = PrettyPrinter(color=False).print
#                ppp('run subgoal', passenger, '::', passenger_stype)
#                ppp('  in mode:', set(V), '==> +', set(vars(passenger) - set(V)))
#                ppp('  guarantees:', set(C), '==>', '+', set(C2 - C))
#                assert C <= C2

                if DEBUG:
                    print(indent+'  ',
                          m('max passengers'), q,
                          m('for'), passenger_stype,
                          m('given'), set(vars(passenger_stype) & V) or {})

                t += q * self._suffixtime(
                    subst1((suffix - {passenger})),
                    subst1(C2),
                    subst1(frozenset(V | set(vars(passenger)))),   # [2022-01-17 Mon] assumes fully bound return, can generalize to other modes later.
                )

            best ^= t

            if DEBUG: print(indent, colors.yellow % 'cost:', t)

        return Param(1) + best

    def lookup(self, b, subst):

        if self.S.chart.is_builtin(b):
            # XXX: we (naively) assume that only fully bound builtins will run.
            #if vars(b) <= subst:
            #warnings.warn('naughty builtin assumption')
            yield (subst, Rule(b, b))

        for s in self.S.chart:
            subst1 = subst.copy().mgu(s.head, b)
            if subst1 is None: continue
            yield (subst1, subst1(Rule(b, *s.body)))
