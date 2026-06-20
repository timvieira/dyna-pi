"""
Built-in relations.
"""

import numpy as np
from dyna.term import (
    unify, Var, Term, unifies, deref, snap, fresh, covers, is_var, Product,
    canonicalize, same, is_ground
)
from dyna.rule import Rule
from dyna.exceptions import InstFault, NotBuiltin
from dyna import syntax
#from dyna.util import to_cons, topython_list


def isbool(Q): return isinstance(Q, bool)
def isint(Q): return isinstance(Q, (np.int32, np.int64, int))
def isnum(Q): return isinstance(Q, (float, int, bool, np.int64, np.int32, np.float32, np.float64))
def isstr(Q): return isinstance(Q, str)
def isvar(Q): return isinstance(Q, Var)

def assert_type(x, t):
    if not isinstance(x, t): raise InstFault(f'expected {t.__name__}, got {x!r}')
    return x


class BuiltinConstraint(Term):

    def run(self, program):
        raise NotImplementedError()


class NotMatchesConstraint(BuiltinConstraint):

    def run(self, program):
        q = self
        assert q.fn == '$not_matches'
        [get_x, y] = q.args
        x = syntax.term(get_x) if isinstance(get_x, str) else get_x()
        if unifies(x, y):
            # $not_matches("p("ROOT",0,N)",p($X0,$X1,$X2)) ==> keep
            if not covers(x, y):   # every item y will be an instance of x
                r = Rule(q, q)    # returns a delayed subgoal
                r.i = None
                yield r
            else:
                return    # subgoal fails
        else:   # statically does not match -> safe to drop the subgoal
            r = Rule(q, program.Semiring.one)
            r.i = None
            yield r
        return


# Comparison builtins: functor -> the Python predicate that evaluates it once
# both arguments are ground.  Shared by every evaluation site (`Program.lookup`
# and both solvers' `lookup_vals`).
cmps = {'<':  lambda x, y: x < y,
        '>':  lambda x, y: x > y,
        '!=': lambda x, y: x != y,
        '==': lambda x, y: x == y,
        '<=': lambda x, y: x <= y,
        '>=': lambda x, y: x >= y}


# The operators the `is` RHS dispatch (Builtins._dispatch) knows how to evaluate.
# Single source of truth used at the dispatch fall-through to distinguish a recognized
# operator whose args aren't ready yet (-> InstFault, delay) from an unrecognized RHS
# operator, i.e. a user predicate (-> NotBuiltin, route to indirect evaluation).
IS_RHS_OPS = {'-', '+', 'abs', 'str', 'int', '!',
              '*', '/', 'min', 'max', 'range'} | set(cmps)


# (functor, arity) signatures of every recognized builtin.  This is the single
# source of truth for classification (`is_builtin`); the comparison ops are
# derived from `cmps` so the two can't drift (a separate hand-written copy in
# `Program.is_builtin` previously omitted `==`, so analyses misclassified
# `X == Y` as an ordinary item).
BUILTIN_SIGS = (
    {('is', 2), ('=', 2), ('$free', 1), ('$bound', 1), ('$not_matches', 2)}
    | {(op, 2) for op in cmps}
)


def is_builtin(x):
    "True iff `x` is a builtin subgoal (a variable, a builtin constraint, or a recognized `(functor, arity)`)."
    x = snap(x)
    if is_var(x): return True
    if isinstance(x, BuiltinConstraint): return True
    return isinstance(x, Term) and (x.fn, x.arity) in BUILTIN_SIGS


class lam:
    def __init__(self, x):
        self.x = x
    def __call__(self):
        return self.x
    def __repr__(self):
        return f'"{self.x}"'
    def __eq__(self, other):
        return isinstance(other, lam) and same(self.x, other.x)
    def __hash__(self):
        return hash(canonicalize(self.x))


def not_matches3(a, b):
    if is_var(snap(a)):     return           # statically false
    elif not unifies(a, b): yield Product()  # statically true
    else:                                    # statically unknown
        yield Product((NotMatchesConstraint('$not_matches', lam(a), b),))


class Builtins:

    def __init__(self, solver):
        self.solver = solver

    def __repr__(self):
        return '<Builtins>'

    def is_ready(self, q):
        "Check if q is ready to run given its current instantiation state."
        q = deref(q)
        if q.fn == '=':
            return True
        else:
            try:
                for _ in self(fresh(q)): pass
            except InstFault:
                return False
            else:
                return True

    def __call__(self, q):
        # Run the pure builtin dispatch.  If the `is` RHS operator is not a builtin (a
        # user predicate), `_dispatch` raises NotBuiltin and we fall back to indirect
        # evaluation (a solver callback).  InstFault (wrong mode / not ready) propagates
        # as before, so `is_ready` can delay the subgoal.
        try:
            yield from self._dispatch(q)
        except NotBuiltin:
            yield from self._indirect_is(q)

    def _indirect_is(self, q):
        # Indirect evaluation of `Value is UserItem`: evaluate the user item with a
        # FULLY-CONVERGED sub-query (`user_query`) and bind Value to its value.  We do
        # NOT peek at the in-progress chart (its values may not be converged; reading
        # them would need retraction -- a different solver).  `is/2` is a constraint: it
        # contributes semiring one per solution (zero if none); the value flows to the
        # LHS via unification.  Guards: (1) mode `-Value is +Key` only -- reject
        # `+Value is -Key`; (2) every result head/value must be GROUND (user_query
        # CONSOLIDATES, so ground heads are automatically disjoint).
        # NOTE: no stratification check yet -- a predicate reaching itself through `is/2`
        # will not terminate.  (Pure stratified use is transformable back to pure dyna.)
        [s, v, k] = deref(q)
        v = snap(v)
        prog = getattr(self.solver, 'program', None)
        if prog is None and hasattr(self.solver, 'user_query'):
            prog = self.solver        # the wiring passed a Program directly
        if prog is None:
            raise InstFault(f'`{q}`: indirect `is` requires a solver/program context.')
        if not is_var(v):
            raise InstFault(
                f'`{q}`: unsupported mode `+Value is -Key` for indirect `is` '
                f'(cannot invert a value back to a key).'
            )
        for r in prog.user_query(fresh(k)).rules:
            body = list(r.body)
            if not (is_ground(r.head) and len(body) == 1 and is_ground(body[0])):
                raise InstFault(
                    f'`{q}`: indirect `is` requires ground results; got {r!r}.'
                )
            for _ in unify(k, r.head):
                yield from unify(v, body[0])

    def _dispatch(self, q):
        [s,v,k] = q = deref(q)

        v = snap(v)

        if s == '=' and q.arity == 2:
            yield from unify(v, k)

        else:
            assert s == 'is' and q.arity == 2

            if not isinstance(k, Term):
                raise InstFault(
                    f'`{q}`: RHS of `is` is a literal {k!r}, not an expression. '
                    f'Use `=` instead of `is` for unification.'
                )

            if k.arity == 1:
                # X is Y * Z
                [Y] = k.args; X = v

                if k.fn == '-':
                    if isnum(Y):
                        yield from unify(X, -Y)
                        return
                    if isnum(X):
                        yield from unify(Y, -X)
                        return

                if k.fn == '+':
                    if isnum(Y):
                        yield from unify(X, +Y)
                        return
                    if isnum(X):
                        yield from unify(Y, +X)
                        return

                if k.fn == 'abs':
                    if isnum(Y):
                        yield from unify(X, abs(Y))
                        return
                    if isnum(X):
                        for y in {+X, -X}:
                            yield from unify(Y, y)
                        return

#                if k.fn == 'exp':
#                    if isnum(Y):
#                        yield from unify(X, np.exp(Y))
#                        return
#                    if isnum(X):
#                        yield from unify(Y, np.log(X))
#                        return

#                if k.fn == 'log':
#                    if isnum(Y):
#                        yield from unify(X, np.log(Y))
#                        return
#                    if isnum(X):
#                        yield from unify(Y, np.exp(X))
#                        return

#                if k.fn == 'sigmoid':
#                    # XXX: needs value -1 <= X <= +1 to invert
#                    if isnum(Y):
#                        yield from unify(X, scipy.special.expit(Y))
#                        return
#                    if isnum(X):
#                        yield from unify(Y, scipy.special.logit(X))
#                        return

#                if k.fn == 'logit':
#                    # XXX: needs value -1 <= X <= +1 to invert
#                    if isnum(Y):
#                        yield from unify(X, scipy.special.logit(Y))
#                        return
#                    if isnum(X):
#                        yield from unify(Y, scipy.special.expit(X))
#                        return

                if k.fn == 'str':
                    if not isvar(Y):
                        yield from unify(X, isstr(snap(Y)))
                        return

                if k.fn == 'int':
                    if not isvar(Y):
                        yield from unify(X, isint(snap(Y)))
                        return
                    else:
                        if isvar(Y) and isbool(X) and X is True:
                            y = 0
                            yield from unify(Y, y)
                            while True:
                                y += 1
                                yield from unify(Y, y)
                                yield from unify(Y, -y)
                            return

                elif k.fn == '!':
                    if not isvar(Y):
                        yield from unify(X, not assert_type(Y,bool))
                        return
                    if not isvar(X):
                        yield from unify(Y, not assert_type(X,bool))
                        return

            if k.arity == 2:

                # X is Y * Z
                Y, Z = k.args; X = v

                X = snap(X)
                Y = snap(Y)
                Z = snap(Z)

                if k.fn == '*':

                    if isstr(Y):
                        if isnum(Z):
                            yield from unify(X, Y * Z)
                            return
                        # TODO: we can solve for K in some cases, e.g., `"aaaaa" is "a" * K`.
                        # Can't multiply string by anything other than an int.
                        raise TypeError(q)

                    else:
                        # numeric cases
                        if isnum(Y) and isnum(Z):
                            yield from unify(X, Y * Z)
                            return
                        if isnum(X) and isnum(Y):
                            yield from unify(Z, X / Y)
                            return
                        if isnum(X) and isnum(Z):
                            yield from unify(Y, X / Z)
                            return

                        # identity elements
                        if isnum(Y) and Y == 1:
                            yield from unify(X, Z)
                            return
                        if isnum(Z) and Z == 1:
                            yield from unify(X, Y)
                            return

                elif k.fn == '+':

                    # string cases
                    if isstr(Y) and isstr(Z):
                        yield from unify(X, Y + Z)
                        return
                    if isstr(X):
                        # loop over splits of the string
                        for k in range(len(X)+1):
                            yield from unify([Y, Z], [X[:k], X[k:]])
                        return

                    # number cases
                    if isnum(Y) and isnum(Z):
                        yield from unify(X, Y + Z)
                        return
                    if isnum(X) and isnum(Y):
                        yield from unify(Z, X - Y)
                        return
                    if isnum(X) and isnum(Z):
                        yield from unify(Y, X - Z)
                        return

                    # identity elements
                    if isnum(Y) and Y == 0:
                        yield from unify(X, Z)
                        return
                    if isnum(Z) and Z == 0:
                        yield from unify(X, Y)
                        return

                elif k.fn == '/':
                    # Just rewrites `X is Y / Z` ==> Y is X * Z =
                    yield from self(Term('is', Y, Term('*', X, Z)))
                    return

                elif k.fn == '-':
                    # Just rewrites `X is Y - Z` ==> Y is X + Z
                    yield from self(Term('is', Y, Term('+', X, Z)))
                    return

                elif k.fn == '>':
                    if not isvar(Y) and not isvar(Z):
                        yield from unify(X, Y > Z)
                        return

                elif k.fn == '<':
                    if not isvar(Y) and not isvar(Z):
                        yield from unify(X, Y < Z)
                        return

                elif k.fn == '>=':
                    if not isvar(Y) and not isvar(Z):
                        yield from unify(X, Y >= Z)
                        return

                elif k.fn == '<=':
                    if not isvar(Y) and not isvar(Z):
                        yield from unify(X, Y <= Z)
                        return

                elif k.fn == '==':
                    if not isvar(Y) and not isvar(Z):
                        yield from unify(X, Y == Z)
                        return

                elif k.fn == '!=':
                    if not isvar(Y) and not isvar(Z):
                        yield from unify(X, Y != Z)
                        return

                elif k.fn == 'min':
                    if not isvar(Y) and not isvar(Z):
                        yield from unify(X, min(Y, Z))
                        return

                elif k.fn == 'max':
                    if not isvar(Y) and not isvar(Z):
                        yield from unify(X, max(Y, Z))
                        return

            if k.arity == 3:
                # true is range(X, A, B)
                X, A, B = k.args

                A = snap(A)
                B = snap(B)

                if k.fn == 'range' and isint(A) and isint(B) and isbool(v) and v == True:
                    for x in range(A, B):
                        yield from unify(X, x)
                    return

            # Fall-through: no op-block handled `k`.  Distinguish a recognized operator
            # whose args aren't ready (delay -> InstFault) from an unrecognized RHS
            # operator -- a user predicate -> NotBuiltin, which `__call__` turns into
            # indirect evaluation.
            if k.fn in IS_RHS_OPS:
                raise InstFault(f'query `{q}` is not supported in this mode')
            raise NotBuiltin(
                f'`{q}`: RHS operator {k.fn!r}/{k.arity} is not a builtin '
                f'(treating as indirect evaluation).'
            )
