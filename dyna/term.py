"""
Generic term representation
"""

from orderedset import OrderedSet
from contextlib import contextmanager


OCCURS_CHECK_ENABLED = True

# we use Ellipsis as a sentinel value since None is a valid value in our Term
# universe.
null_ptr = Ellipsis
#cdef null_ptr = object()    # this does not work with deepcopy or pickle
#cdef class null_ptr: pass    # this version does work with deepcopy and pickle


def gen_functor(prefix='$gen'):
    gen_functor.i += 1
    return f'{prefix}{gen_functor.i}'
gen_functor.i = 0


def gen_functor_reset():
    gen_functor.i = 0
gen_functor.reset = gen_functor_reset


def gen():
    "Generate a new identifier"
    gen.i += 1
    return f'$Gen{gen.i}'
gen.i = 0


def gen_reset():
    gen.i = 0
gen.reset = gen_reset


def join_f(f, *xs):
    if len(xs) == 0:
        yield Product()
    else:
        for d1 in f(xs[0]):
            for d2 in join_f(f, *xs[1:]):
                yield d1 * d2

#def join(f, xs):
#    assert isinstance(xs, tuple), xs
#    if len(xs) == 0: yield ()
#    else:
#        for d1 in f(xs[0]):
#            for d2 in join(f, xs[1:]):
#                yield (d1, *d2)
#
#
#def joinv(f, xs, one):
#    assert isinstance(xs, tuple), xs
#    if len(xs) == 0: yield one
#    else:
#        for d1 in f(xs[0]):
#            for d2 in joinv(f, xs[1:], one):
#                yield d1 * d2

# TODO: untested
#def explicit_sips(f, x, subst0):     # assumes the function f returns a stream of pairs
#    assert isinstance(x, tuple), x
#    if len(x) == 0:
#        yield (), subst0
#    else:
#        # sideways information passing
#        for V1, subst1 in f(x[0], subst0.copy()):
#            for V2, subst2 in explicit_sips(f, x[1:], subst1.copy()):
#                yield (V1, *V2), subst2


def flatten(x):
    "Flatten the nested conjunctions."
    yield from flatten_op(x, ',')


def flatten_op(x, op):
    "Flatten the nested conjunctions."
    x = snap(x)
    if isinstance(x, Term) and x.fn == op:
        for y in x.args:
            yield from flatten_op(y, op)
    else:
        yield x


class Var:
    "Runtime variable"

    __slots__ = ('name', 'value')

    def __init__(self, name=None):
        assert isinstance(name, str) or name is None
        # the name is optional; only used for pretty-printing
        self.name = name if name is not None else gen()
        self.value = null_ptr

    # experimental
    def __mul__(self, y):
        if not isinstance(y, tuple): y = (y,)
        return Product((self, *y))

    def __rmul__(self, y):
        if not isinstance(y, tuple): y = (y,)
        return Product((*y, self))

    def occurs_check(self, x):
        """
        Return true if variable var occurs anywhere in x
        (or in subst(s, x), if s has a binding for x).
        """
        if OCCURS_CHECK_ENABLED:
            if self is x:
                return True
            elif isinstance(x, Var) and x.is_bound():
                return self.occurs_check(x.value)
            elif isinstance(x, (Term, list, tuple)):
                for e in x:
                    if self.occurs_check(e):
                        return True
                return False
        else:
            return False   # unsafe, but should be significantly faster

    def __repr__(self, **kwargs):
        return pp(self, **kwargs)

    def is_bound(self):
        return self.value is not null_ptr

    def __hash__(self):
        if self.is_bound():
            return hash(self.value)
        else:
            return object.__hash__(self)

    def __eq__(self, other):
        x = snap(self)
        y = snap(other)
        xv = isinstance(x, Var)
        yv = isinstance(y, Var)
        if not xv and not yv:
            return x == y      # two values
        else:
            return x is y      # one or more variables

    def __lt__(self, other):
        return lt(self, other)


class Product(tuple):

    def __mul__(self, other):
        if not isinstance(other, tuple): other = (other,)
        return Product((*self, *other))

    def __rmul__(self, other):
        if not isinstance(other, tuple): other = (other,)
        return Product((*other, *self))

    def __getitem__(self, xs):
        if isinstance(xs, (tuple, dict, list)):
            return Product([super(Product, self).__getitem__(x) for x in xs])
        if isinstance(xs, slice):
            return Product(super(Product, self).__getitem__(xs))
        return super(Product, self).__getitem__(xs)

    def __repr__(self, **kwargs):
        return pp(self, **kwargs)

    def snap_unifications(self):
        if len(self) == 0:
            yield Product()
            return
        if isinstance(self[0],Term) and self[0].fn == '=':
            [_,a,b] = self[0]
            for _ in unify(a,b):
                yield from self[1:].snap_unifications()
        else:
            for ys in self[1:].snap_unifications():
                yield self[0] * ys

    def covers(self, ys, s=Ellipsis):
        """
        Lazily enumerate matches from subgoal list `xs` to subgoal list `ys`.
        Each iterate is a tuple (substitution map, index-index alignment, coverage set).

        Substitutions maps θ and alignment are such that

            θ(xs[i]) == ys[j]   for all j,i in alignment.items()
            alignment is a one-to-one function from indices of xs to the indices of ys.

        """
        assert isinstance(self, Product) and isinstance(ys, Product)
        if s is Ellipsis: s = Subst()
        yield from self._covers(ys, i=0, js=set(range(len(ys))), s=s)

    def _covers(
            self, y,
            i: 'cursor into x',
            js: 'available indices in y',
            s: 'current substitution map',
    ):

        if s is FAIL: return FAIL

        if i == len(self):
            yield (s, {}, sorted(js))
            return

        if len(self) - i > len(js): return

        # XXX: Below are some heuristics to short-circuit backtracking sooner.
#        if USE_HEURISTIC:
#            try:
#                xx = Counter([(X.fn, X.arity) for X in x[i:]])
#                yy = Counter([(y[j].fn, y[k].arity) for j in js])
#                for a in xx:
#                    if xx[a] > yy[a]:  # if we don't have enough `a`s in y to cover x, quit now.
#                        #STOP += 1
#                        return
#            except AttributeError:  # had a variable
#                pass

        for j in js:
            for (S, A, R) in self._covers(y, i+1, js - {j}, s.copy().cover(self[i], y[j])):
                yield (S, {**A, j: i}, R)

    # Note: this method is many used to test equality, but subsumption.  For subsumption use covers.
    def match_comm(self, other, i=0, js=None, s=Ellipsis):
        if js is None: js = frozenset(range(len(other)))
        if s is Ellipsis: s = Subst()
        assert (isinstance(other, (tuple, Product)) and isinstance(i, int)
                and isinstance(js, frozenset) and isinstance(s, Subst))
        yield from self._match_comm(ys=other, i=i, js=js, s=s)

    def _match_comm(
        self, ys,
        i: 'cursor into x',
        js: 'available indices in y',
        s: 'current substitution map',
    ):
        if s == FAIL: return
        if i == len(self):
            yield s
            return
        if len(self) - i != len(js): return
        for j in sorted(js):
            yield from self._match_comm(ys=ys, i=i+1, js=js - {j}, s=s.copy().cover(self[i], ys[j]))

    # TODO: subproduct and cover should have the same API
#    def subproduct(self, ys):
#        "enumerate continguous subproducts of `self` (for non-commutative semirings)."
#        xs = self
#        N = len(xs)
#        M = len(ys)
#        for j in range(M - N + 1):
#            s = Subst()
#            fail = False
#            for i in range(N):
#                if s.cover(xs[i], ys[j+i]) is None:
#                    fail = True
#                    break
#            if not fail:
#                yield s, j


class Term:

    def __init__(self, *fargs):
        self.fargs = fargs

    # experimental
    def __mul__(self, y):
        if not isinstance(y, tuple): y = (y,)
        return Product((self, *y))
    def __rmul__(self, y):
        if not isinstance(y, tuple): y = (y,)
        return Product((*y, self))
#    def __mul__(self, y):  return Term('*', self, y)
#    def __rmul__(self, y): return Term('*', y, self)
#    def __add__(self, y):  return Sum(self, y)
#    def __radd__(self, y): return Sum(y, self)

    def fresh(self, m):
        y = self.__class__(*[m(a) for a in self.fargs])
        if hasattr(self, 'i'): y.i = self.i    # annoying bookkeeping
        return y

    def sub(self, s):
        y = self.__class__(*s(self.fargs))
        if hasattr(self, 'i'): y.i = self.i    # annoying bookkeeping
        return y

    @property
    def fn(self):
        return snap(self.fargs[0])

    @property
    def args(self):
        return self.fargs[1:]

    @property
    def arity(self):
        return len(self)-1

    def __len__(self):
        return len(self.fargs)

    def __repr__(self, **kwargs):
        return pp(self, **kwargs)

    def __iter__(self):
        return iter(self.fargs)

    def __hash__(self):
        return hash(self.fargs)

    def __eq__(self, other):
        other = snap(other)
        return isinstance(other, Term) and self.fargs == other.fargs

    def __lt__(self, other):
        return lt(self, other)


#_______________________________________________________________________________
# Unification

def unify(x, y):
    "Attempt to unify `x` with `y`."
    if x == y:
        yield
    elif isinstance(x, Var):

        if x.is_bound():
            yield from unify(x.value, y)

        elif isinstance(y, Var) and y.is_bound():
            yield from unify(x, y.value)

        elif not x.occurs_check(y):
            was = x.value
            x.value = y
            try:
                yield

            # No matter what (e.g., an exception) we revert the value back.
            # This means that if this iterator gets garbage collected (because
            # there are no references to it) the finally block will run and the
            # unifications will get undone.  This makes it very hard to have
            # unmanaged/stateful unifications.  We used to be able to unify
            # without the looping pattern and have sideffects, but that is not
            # longer the case.
            finally:
                x.value = was

    elif isinstance(y, Var):
        yield from unify(y, x)    # pylint: disable=W1114

    elif isinstance(x, (Term, list, tuple)) and isinstance(y, (Term, list, tuple)) and len(x) == len(y):
        yield from unifyN(x, y)


def unifyN(xs, ys):
    "Attempt to unify two sequences, `xs` and `ys`, assumed to have equal length."
    assert len(xs) == len(ys)
    if len(xs) == 0:
        yield
    else:
        x,*xs = xs
        y,*ys = ys
        for _ in unify(x, y):
            yield from unifyN(xs, ys)


#______________________________________________________________________________
# Unification algorithms 2.0 -- getting rid of annoying side-effects.
#
# Implementation based on
# https://github.com/aimacode/aima-python/blob/master/logic.py

# TODO: we could have a special nonspecializing substitution class that give a
# unification failure sooner and uses more bookkeeping for faster detection
class Subst(dict):

    def __call__(self, x):
        if x in self:
            return self(self[x])
        elif isinstance(x, Var):  # var is not in s.
            return x
        elif isinstance(x, Term):
            return x.sub(self)
        elif isinstance(x, tuple):
            return tuple([self(arg) for arg in x])
        else:
            #assert isinstance(x, (int, float, str)), x
            return x

    #def apply_once(self, x):
    #    if x in self:
    #        return self[x]
    #    elif isinstance(x, Var):  # var is not in s.
    #        return x
    #    elif isinstance(x, Term):
    #        return Term(x.fn, *self.apply_once(x.args))
    #    elif isinstance(x, tuple):
    #        return tuple([self.apply_once(arg) for arg in x])
    #    else:
    #        #assert isinstance(x, (int, float, str)), x
    #        return x

    def is_non_specializing(self):
        "Check that `s` is a variable-to-variable bijection"
        # Can only map to variables
        if not all(isinstance(v, Var) for v in self.values()):
            return False
        # the number of distinct variables must be equal.
        if len(self.keys()) != len(set(self.values())):
            return False
        return True

    def occur_check(self, var, x):
        """Return true if variable `var` occurs anywhere in x
        (or in subst(s, x), if s has a binding for x)."""
        if not OCCURS_CHECK_ENABLED: return False
        if var == x:
            return True
        elif isinstance(x, Var) and x in self:
            return self.occur_check(var, self[x])
        elif isinstance(x, Term):
            return any(self.occur_check(var, y) for y in x.fargs)
        else:
            return False

    def mgu(self, x, y):
        #if self is FAIL: return FAIL
        if x == y: return self
        elif isinstance(x, Var):
            if x in self:
                return self.mgu(self[x], y)
            elif y in self:
                return self.mgu(x, self[y])
            elif self.occur_check(x, y):
                return FAIL
            else:
                self[x] = y
                return self
        elif isinstance(y, Var):
            return self.mgu(y, x)       # pylint: disable=W1114
        elif isinstance(x, Term) and isinstance(y, Term) and x.arity == y.arity:
            s = self
            for a, b in zip(x.fargs, y.fargs):
                s = s.mgu(a, b)
                if s is FAIL: return FAIL
            return s
        else:
            return FAIL

    def cover(self, x, y):
        "Helper method for `covers(x,y)`. Note: calls mutate `s`."
        x = snap(x); y = snap(y)

        if x == y:
            return self

        elif isinstance(x, Var):
            if x in self:
                if self[x] == y:
                    return self
            elif not self.occur_check(x, y):
                self[x] = y            # Note: we do *not* need to copy `s`.
                return self

        elif isinstance(x, Term) and isinstance(y, Term) and x.arity == y.arity:
            s = self
            for a, b in zip(x.fargs, y.fargs):
                s = self.cover(a, b)
                if s is None: return
            return s

    def copy(self):
        return Subst(self)

    def __repr__(self, **kwargs):
        return pp(self, **kwargs)


Subst.FAIL = FAIL = None


#_______________________________________________________________________________
# Covers / Subset

def covers(x, y):
    """
    Check if the set of terms denoted by `x` is a superset of the set of terms
    denoted by `y`.
    """
    return Subst().cover(x, y) is not FAIL

#______________________________________________________________________________
# Fresh variables

class Fresh:

    def __init__(self, nice_name=True, m=Ellipsis):
        self.m = {} if m is Ellipsis else m
        self.nice_name = nice_name

    def __call__(self, x):
        m = self.m
        if isinstance(x, Var) and x.is_bound():
            return self(x.value)
        elif isinstance(x, Var):
            if x not in m:         # already refreshed
                m[x] = Var(x.name if self.nice_name else None)    # use the original name
            return m[x]
        elif isinstance(x, Term):
            return x.fresh(self)
        elif isinstance(x, tuple):
            return tuple(self(a) for a in x)
        else:
            return x    # constants


def fresh(z, nice_name=True):
    "Allocate fresh variables in Terms, sets, etc."
    return Fresh(nice_name)(z)


#______________________________________________________________________________
# Anti-unification

def generalizer(t1, t2, s1=Ellipsis, s2=Ellipsis):
    "Anti-unification algorithm"

    if s1 is Ellipsis: s1 = {}
    if s2 is Ellipsis: s2 = {}

    def traverse(x, y):

        if x == y:
            return x

        elif isinstance(x, Var):   # x != y and x is a variable

            if x.occurs_check(y):
                if x not in s1:
                    s1[x] = Var()
                return s1[x]

            if x in s1:             # already have an subst for `x`, it must match.
                if s1[x] != y:
                    s1[x] = Var()
                    return s1[x]
            else:
                s1[x] = y            # Note: we do *not* need to copy `s`.
            return x

        elif isinstance(y, Var):   # x != y, x is not a variable, y is a variable

            if y.occurs_check(x):
                if y not in s2: s2[y] = Var()
                return s2[y]

            if y in s2:
                if s2[y] != x:
                    s2[y] = Var()
                    return s2[y]
            else:
                s2[y] = x            # Note: we do *not* need to copy `s`.
            return y

        elif isinstance(x, Term) and isinstance(y, Term) and len(x) == len(y) and x.fn == y.fn:
            return Term(*(traverse(a, b) for a, b in zip(x, y)))

        else:
            if x in s1:
                return s1[x]
            if y in s2:
                return s2[x]

            z = Var()
            s1[x] = z
            s2[y] = z
            return z

    return traverse(t1, t2)

#______________________________________________________________________________
# HELPERS

def is_var(x):
    return isinstance(snap(x), Var)

#def is_bound(x):
#    return not is_free(x)

#def is_free(x):
#    return is_var(x)

#def is_const(x):
#    return not isinstance(snap(x), (Var, Term))


def lt(x, y):
    x = snap(x)
    y = snap(y)

    if x == y:
        return False

    elif isinstance(x, Var):
        # any thing is < a variable except a variable with a < name.
        return isinstance(y, Var) and x.name < y.name

    elif isinstance(x, Term):

        if isinstance(y, Term):
            for i in range(min(x.arity, y.arity)+1):
                if x.fargs[i] == y.fargs[i]:
                    continue
                elif lt(x.fargs[i], y.fargs[i]):
                    return True
                else:
                    return False
            # All common slots are equal, take the lower arity term as the min.
            return (x.arity < y.arity)

        else:
            return lt(x.fn, y)

    elif isinstance(y, (Var, Term)):
        return not (y < x)

    else:

        try:
            return x < y
        except TypeError:
            return type(x).__name__ < type(y).__name__


def is_ground(x):
    if isinstance(x, Var):
        return x.is_bound() and is_ground(x.value)
    elif isinstance(x, (Term, list, tuple)):
        return all(map(is_ground, x))
    else:
        return True


def snap(x):
    return snap(x.value) if isinstance(x, Var) and x.is_bound() else x


#______________________________________________________________________________
#

def canonicalize(X):
    "canonicalize(x) == canonicalize(y) ⇔ same(x,y)."
    return _canonicalize(X, vs={})


def _canonicalize(x, vs):
    x = snap(x)

    if isinstance(x, Var):
        y = vs.get(id(x))
        if y is not None:
            return y
        else:
            y = vs[id(x)] = _canonicalize_var(len(vs))
            return y

    elif isinstance(x, Term):
        return x.__class__(*[_canonicalize(y, vs) for y in x.fargs])

#    elif isinstance(x, list):
#        return [_canonicalize(a, vs) for a in x]

#    elif isinstance(x, tuple):
#        return tuple([_canonicalize(a, vs) for a in x])

    # TODO: dict?
#    elif isinstance(x, (set, frozenset)):
#        return frozenset([_canonicalize(k, vs) for k in sorted(x)])

    else:
#        assert isinstance(x, (str, int, float)), x
        return x


_cvars = []
def _canonicalize_var(i):
    for _ in range(len(_cvars), i+1):
        _cvars.append(Var(f'$X{i}'))
    return _cvars[i]


#______________________________________________________________________________
#


def vars(x, vs=None):
    "Extract all variables from `x`."
    if vs is None: vs = OrderedSet()

    if isinstance(x, Var):
        if x.value is null_ptr:
            vs.add(x)   # free variable
            return vs
        else:
            return vars(x.value, vs)

    elif isinstance(x, (Term, list, tuple, set, OrderedSet)):
        for y in x:
            vars(y, vs)

    elif isinstance(x, Stream):
        vs |= x.vars

    return vs


def unifies(A, B):
    "Intersection"
    u = False
    for _ in unify(A, B):
        u = True
    return u


def same(x, y):
    "Set equivalence"
#    s = Subst().mgu(x,y)
#    return s is not s.FAIL and s.is_non_specializing()
    return covers(x, y) and covers(y, x)   # pylint: disable=W1114


def intersect(x, y):
    "Create a fresh term that represents the interesection of terms `x` and `y`."
    z = None
    for _ in unify(x, y):
        z = fresh(x)
    return z


def replace_in_expr(expr, target, replacement):
    """
    Replace all occurrences of `target` with `replacement` in `expr`.
    """
    expr = snap(expr)
    target = snap(target)
    replacement = snap(replacement)
    if expr == target:
        return replacement
    elif isinstance(expr, Term):
        return expr.__class__(*replace_in_expr(expr.fargs, target, replacement))
    elif isinstance(expr, tuple):
        return tuple(replace_in_expr(x, target, replacement) for x in expr)
    else:
        return expr


# Implementation note: `deref` is not a method on `Var` and `Term` because we
# might call it on other types such as int and str.
def deref(x):
    "Recursive pointer snapping on variables."
    if isinstance(x, Var):
        return deref(x.value) if x.is_bound() else x
    elif isinstance(x, Term):
        return x.__class__(*deref(x.fargs))   # works with subclasses
    elif isinstance(x, tuple):
        return tuple(deref(y) for y in x)
    else:
        return x


class FreshCache:

    def __init__(self):
        self._cache = {}
        self._objects = []   # keep a reference o/w we might recycle id's!

    @contextmanager
    def __call__(self, r):
        i = id(r)
        if i not in self._cache:
            self._cache[i] = []
            self._objects.append(r)   # keep a reference to r
        cache = self._cache[i]
        s = cache.pop() if cache else fresh(r)
        yield s
        cache.append(s)


class NoDupsSet:
    def __init__(self, xs, same):
        self.same = same
        self.xs = []
        for x in xs: self.add(x)
    def __len__(self): return len(self.xs)
    def __iter__(self): return iter(self.xs)
    def add(self, r):
        """
        Add r to the collection.
        Returns True if r was subsumed by a more general rule in the program
        Returns False otherwise.
        """
        # This implementation is pretty inefficient as it is based on linear scan
        for s in self.xs:
            # branch r is already contained in set
            if self.same(r, s):    # pylint: disable=W1114
                return True
        self.xs.append(r)
        return False
    def find(self, x):
        "Return the node in the set that covers x"
        for i, s in enumerate(self.xs):
            if self.same(s, x):
                return i
        raise KeyError(f'did not find {x} in {self}')
    def root(self, x):
        return self.xs[self.find(x)]
    def __repr__(self):
        return repr(set(self.xs) or {})


class MostGeneralSet:
    def __init__(self, xs, covers):
        self.covers = covers
        self.xs = []
        for x in xs: self.add(x)
    def __len__(self): return len(self.xs)
    def __iter__(self): return iter(self.xs)
#    def __getitem__(self, *args): return self.xs.__getitem__(*args)
    def add(self, r):
        """
        Add r to the collection.
        Returns True if r was subsumed by a more general rule in the program
        Returns False otherwise.
        """
        # This implementation is pretty inefficient as it is based on linear scan
        rm = []
        for i, s in enumerate(self.xs):
            # branch r is already subsumed by branch s
            if self.covers(s, r):    # pylint: disable=W1114
                return True
            # new branch subsumes existing branch, will be deleted in favor of
            # the more general branch.
            if self.covers(r, s):
                rm.append(i)
        for i in reversed(sorted(rm)):
            del self.xs[i]
        self.xs.append(r)
        return False
    def find(self, x):
        "Return the node in the set that covers x"
        for i, s in enumerate(self.xs):
            # branch r is already subsumed by branch s
            if self.covers(s, x):    # pylint: disable=W1114
                return i
        raise KeyError(f'did not find a cover for {x} in {self}')
    def root(self, x):
        return self.xs[self.find(x)]
    def __repr__(self):
        if self.xs:
            return 'MostGeneralSet {\n%s\n}' % ('\n'.join(f'  {x},' for x in self))
        else:
            return 'MostGeneralSet {}'


class DisjointEstimate:
    """
    Maintain a running upper bound on the union of a set of terms; uses
    anti-unification to prevent the sets from getting to complicated.
    """
    def __init__(self, xs=()):
        self.xs = []
        for x in xs: self.add(x)
    def __len__(self): return len(self.xs)
    def __iter__(self): return iter(self.xs)
#    def __getitem__(self, *args): return self.xs.__getitem__(*args)
    def root(self, x): return self.xs[self.find(x)]
    def __repr__(self):
        if self.xs:
            return 'DisjointEstimate {\n%s\n}' % ('\n'.join(f'  {x},' for x in self))
        else:
            return 'DisjointEstimate {}'
    def add(self, r):
        "Add r to the collection while maintaining disjointness."
        # This implementation is pretty inefficient as it is based on linear scan
        for i in reversed(range(len(self.xs))):       # back to front so we can delete
            if unifies(r, self.xs[i]):   # overlaps
                r = generalizer(r, self.xs[i])
                del self.xs[i]
        self.xs.append(canonicalize(r))
    def find_all(self, x):
        "Return the unique branch of the partition that x falls into (or throw an error)"
        index = []
        for i, s in enumerate(self.xs):
            if unifies(x, s):
                index.append(i)
        return index
    def find(self, x):
        index = self.find_all(x)
        if len(index) == 0:
            raise KeyError(f'did not find any type for {x} in {self}')
        elif len(index) == 1:
            return index[0]
        else:
            raise KeyError(f'did not find a unique type for {x} in {self}')
    def roots(self, x):
        "Return the unique branch of the partition that x falls into (or throw an error)"
        return [self.xs[i] for i in self.find_all(x)]
    def to_program(self):
        from dyna import Program, Rule
        return Program([Rule(x) for x in self])



class Stream:

    def __mul__(self, other):
        assert isinstance(other, Stream), other
        return Join(self, other)
#    def __add__(self, other):
#        return Union(self, other)
#    def __rmatmul__(self, f):
#        return Proj(f, self)
#    @classmethod
#    def sum(cls, elems):
#        y = cls.zero
#        for x in elems:
#            y += x
#        return y
#    @classmethod
#    def product(cls, elems):
#        elems = list(elems)
#        if len(elems) == 0:
#            # empty Product actuals as a neutral element for the (unknown) semiring
#            return Constant(Product())
#        y = elems[0] if isinstance(elems[0], Stream) else Constant(elems[0])
#        for x in elems[1:]:
#            if not isinstance(x, Stream): x = Constant(x)
#            y *= x
#        return y


class ResultStream(Stream):
    def __init__(self, f, *args):
        self.f = f
        self.args = args
        self.vars = vars(self.args)
    def __iter__(self):
        return iter(self.f(*self.args))
    def __repr__(self):
        if len(self.args) == 1:
            return f'${self.f.__name__}({self.args[0]})'
        return f'${self.f.__name__}{self.args}'


class Join(Stream):
    def __init__(self, xs, ys):
        assert isinstance(xs, Stream) and isinstance(ys, Stream)
        self.xs = xs
        self.ys = ys
        self.vars = vars(xs) | vars(ys)
    def __iter__(self):
        for x in self.xs:
            for y in self.ys:
                yield x * y
    def __repr__(self):
        return f'Join({self.xs}, {self.ys})'


#class Union(Stream):
#    def __init__(self, xs, ys):
#        assert isinstance(xs, Stream) and isinstance(ys, Stream)
#        self.xs = xs
#        self.ys = ys
#        self.vars = vars(xs) | vars(ys)
#    def __iter__(self):
#        yield from self.xs
#        yield from self.ys


#class Proj(Stream):
#    def __init__(self, f, xs):
#        self.f = f
#        self.xs = xs
#        self.vars = vars(xs)
#    def __iter__(self):
#        for x in self.xs:
#            yield self.f(x)


#def _z():
#    if 0: yield
#ResultStream.zero = ResultStream(_z)


#def _e(): yield     # FIXME: should be semione, but we don't have a reference to the semiring!
#ResultStream.one = ResultStream(_e)


class I(Stream):
    def __init__(self, x, y, v):
        self.v = v; self.x = x; self.y = y
        self.vars = vars(x) | vars(y) | vars(v)
    def __repr__(self):
        return f'{self.v}[{self.x}={self.y}]'
    def __iter__(self):
        for _ in unify(self.x, self.y):
            yield self.v


class Constant(Stream):
    def __init__(self, v, vs=None):
        self.v = v
        self.vars = vars(v) if vs is None else vs
    def __repr__(self):
        return f'{self.v}'
    def __iter__(self):
        yield self.v


NIL = Term('$nil')


# This import must go at the bottom of the file.
from dyna.pretty import pp
