from dyna import (
    pp, Term, Var, unify, unifies, covers, is_ground, generalizer,
    intersect, same, Subst, canonicalize, deref, Product, gen_functor, fresh,
    PrettyPrinter, gen
)
from dyna import term_
from dyna.syntax import term
from dyna.util import setunset
from arsenal import colors


functor = lambda f: lambda *args: Term(f, *args)


def test_generalizer():

    def check(x, y, want):
        assert isinstance(x, str)
        assert isinstance(y, str)
        assert isinstance(want, str)
        x, y = term(f'tmp({x}, {y})').args

        gen.reset()
        s1 = Subst()
        s2 = Subst()

        have = generalizer(x, y, s1, s2)

        #print('  have:', have)
        #print('  ', colors.magenta % s1)
        #print('  ', colors.magenta % s2)

        #yy = s1.apply_once(have)
        #xx = s2.apply_once(have)

        #print('   x:', x, xx, colors.mark(xx == y))
        #print('   y:', y, yy, colors.mark(yy == x))
        #assert xx == x, [xx, x]
        #assert yy == y, [yy, y]

        if str(have) == str(want):
            print(x, y, '==>', want, colors.mark(True))
        else:
            print(x, y, colors.mark(False))
            print('  have:', have)
            print('  want:', want)
            check.failures += 1
    check.failures = 0

    check('X', 'Y', 'X')             # takes the left argument arbitrarily
    check('f(X)', 'f(Y)', 'f(X)')    # takes the left argument arbitrarily

    check('f(X)', 'f(3)', 'f(X)')
    check('f(3,Y)', 'f(X,4)', 'f(X,Y)')

    check('f(3,3,Y,Y)', 'f(X,X,4,4)', 'f(X,X,Y,Y)')
    check('f(X,X,4,4)', 'f(3,3,Y,Y)', 'f(X,X,Y,Y)')

    # This is some weird occurscheck behavior
    #check('f(X,X,4,4)', 'f(3,3,X,X)', 'f(X,X,X,X)')
    #check('f(X,4,X,4)', 'f(3,3,X,X)', 'f(X,X,X,X)')    # not sure what should happen here

    check('f(X,Y)', 'f(Y,X)', 'f(X,Y)')

    check('f(X,3)', 'f(Y,Y)', 'f(X,Y)')

    check('f(X)', 'g(X)', '$Gen1')
    check('f(X)', 'f(Y,Z)', '$Gen1')
    check('f(X)', 'f(X,Y)', '$Gen1')

    check('f(X,Y,Z)', 'f(X,Y,Z)', 'f(X,Y,Z)')
    check('f(X,Y,Z)', 'f(X,Z,Y)', 'f(X,Y,Z)')
    check('f(X,Y,Z)', 'f(Y,X,Z)', 'f(X,Y,Z)')
    check('f(X,Y,Z)', 'f(Y,Z,X)', 'f(X,Y,Z)')
    check('f(X,Y,Z)', 'f(Z,X,Y)', 'f(X,Y,Z)')
    check('f(X,Y,Z)', 'f(Z,Y,X)', 'f(X,Y,Z)')

    # occurs check cases
    check('f(X)', 'X', '$Gen1')
    check('X', 'f(X)', '$Gen1')

    assert check.failures == 0


def test_misc():

    X = term('X')

    y = X * 2
    assert isinstance(y, Product) and len(y)

    y = 2 * X
    assert isinstance(y, Product) and len(y)

    x = term('f(X)')
    y = x * 2
    assert isinstance(y, Product) and len(y)

    y = 2 * x
    assert isinstance(y, Product) and len(y)

    y = x * x
    assert isinstance(y, Product) and len(y)


def test_canonicalize():

    def check(x, y, eq=True):
        xc = canonicalize(term(x))
        yc = canonicalize(term(y))
        print()
        print(x, '==>', xc)
        print(y, '==>', yc)
        if (xc == yc) == eq:
            print(colors.ok)
        else:
            print(colors.poop)
            assert False

    check('f(X)', 'f(Y)')
    check('f(X,X)', 'f(X,Y)', False)
    check('f(X,g(X))', 'f(Y,g(Y))')
    check('f(X,Y,g(X,Z))', 'f(Y,Z,g(Y,W))')


# [2022-02-14 Mon] The following examples fail because they contain cyclical
# substitutions, which we choose not to handle (for efficiency).
#
#def test_subst():
#
#    W,X,Y,Z = map(Var, 'WXYZ')
#
#    s = {W: X, X: Y, Y: Z, W: Z}
#
#    have = sub((W,X,Y,Z), s)
#    print(have)
#    assert len(set(have)) == 1, set(have)
#
#    print()
#    s = {W: Z, Z: Y, Y: Z, X: Y}
#    print(s)
#    have = sub((W,X,Y,Z), s)
#    print(have)
#    assert len(set(have)) == 1, set(have)
#

def test_unify():

    def test(x, y, fails=False):
        print('unify', x, y)

        # testing the new-school unification algorithms that don't mutate the term.
        s = Subst().mgu(x, y)
        assert (s is Subst.FAIL) == fails
        if not fails:
            xs = s(x)
            ys = s(y)
            assert str(xs) == str(ys), [x, y, xs, ys, s]

        assert fails == (not unifies(x, y))
        assert fails == (not unifies(y, x))

        # I'm assuming that in all cases the terms passed in are initially
        # different, but it would be easy to violate that contract.
        assert x != y

        if not fails:
            for _ in unify(x, y):
                assert hash(x) == hash(y)
                assert x == y, [x, y]
                assert str(x) == str(y), [x,y]
            for _ in unify(y, x):               # pylint: disable=W1114
                assert hash(x) == hash(y)
                assert x == y, [x, y]
                assert str(x) == str(y), [y,x]


    f, g, h = map(functor, 'fgh')
    X, Y, Z, A, B, C = map(Var, 'XYZABC')

    # check that variables unify
    x = X
    y = Y
    test(x, y)

    # check that simplest terms unify
    x = Term('f', X)
    y = Term('f', Y)
    test(x, y)

    x = Term('f', Term('g', X))
    y = Term('f', Y)
    test(x, y)

    x = Term('f', Term('g', X))
    y = Term('f', Term('h', Y))
    test(x, y, fails=True)

    x = Term('f', X)
    y = Term('g', Y)
    test(x, y, fails=True)

    # check that simplest or do not unify
    x = Term('f', X)
    y = Term('g', Y)
    test(x, y, fails=True)

    # Test nested terms
    x = f(A, g(X, B), Z)
    y = f(C, g(1, B), h(Y))
    test(x, y)

    # NWF's example of variable capture
    x = f(X,1)
    y = f(Y,X)
    test(x,y)

    x = Term('f', X)
    y = Term(Var('F'), Y)
    test(x, y)

    # Test Norvig's examples
    p = functor('p')
    q = functor('q')

    x = p(X,Y,5)
    y = p(Y,X,X)
    test(x, y)

    x = p(X,Y)
    y = p(Y,X)
    test(x, y)

    x = q(p(X, Y), p(Y, X))
    y = q(Z, Z)
    test(x, y)


def test_occurs_check():
    f, g, h = map(functor, 'fgh')
    X, Y = map(Var, 'XY')

    with setunset(term_, 'OCCURS_CHECK_ENABLED', True):

        assert X.occurs_check(f(X))
        assert not X.occurs_check(f(Y))
        assert X.occurs_check(f(g(h(X))))

        assert unifies(X, X)
        assert not unifies(X, f(X))
        assert unifies(X, f(Y))
        assert not unifies(X, f(g(h(X))))

    with setunset(term_, 'OCCURS_CHECK_ENABLED', False):

        # when the occurs_check is disabled it simple returns false
        assert not X.occurs_check(f(X))
        assert not X.occurs_check(f(Y))
        assert not X.occurs_check(f(g(h(X))))

        # contrast these examples with the same examples above
        assert unifies(X, X)
        assert unifies(X, f(X))
        assert unifies(X, f(Y))
        assert unifies(X, f(g(h(X))))


    def subst_unifies(x, y):
        return Subst().mgu(x, y) is not Subst.FAIL

    with setunset(term_, 'OCCURS_CHECK_ENABLED', True):
        assert subst_unifies(X, X)
        assert not subst_unifies(X, f(X))
        assert subst_unifies(X, f(Y))
        assert not subst_unifies(X, f(g(h(X))))

    with setunset(term_, 'OCCURS_CHECK_ENABLED', False):
        # contrast these examples with the same examples above
        assert subst_unifies(X, X)
        assert subst_unifies(X, f(X))
        assert subst_unifies(X, f(Y))
        assert subst_unifies(X, f(g(h(X))))


def test_term_comparison():

    X, Y = map(Var, 'XY')

    # Test comparison and equality operationss on terms
#    assert Term("f") == "f"
#    assert not (Term("f") < "f")
#    assert (Term("f") <= "f")
#    assert not (Term("f") > "f")
#    assert Term("goal") > "f"

    x = term('f(X)')
    assert x == x
    assert x != 3
    assert x != "foo"
    assert x != fresh(x)
    assert term('f(X)') != term('f(X)')   # not equal despite the variable name
    assert not (x < x)

    assert term('goal') == term('goal')
    assert not (term('goal') < term('goal'))

    assert term('f(1)') < term('f(1,2)')        # arity
    assert not (term('f(1,2)') < term('f(1)'))  # arity
    assert term('f(1,2,3)') < term('g(1)')      # alphabetical

    assert not (term('f(1,2,3)') < 3)
    assert not (term('f(1,2,3)') < "a")
    #assert "a" < term('f(1,2,3)')        # comparison fails (TypeError)

    assert Term("f", 1) < Term("goal")
    assert Term("f", 1) < Term("f", 10)
    assert Term("f", 1) == Term("f", 1)

    assert Term("f", 1, Term("g", 3)) < Term("f", 1, Term("g", 4))
#    assert Term("f", Term("g", Term("h", 3))) > Term("f", 1, Term("g", 4))

    # comparisons involving variables
    assert Term("f", X) < Term("f", Y)
    assert Term("f", X) < Term("f", Y)   # just because of the variable name
    assert Term("f", Y) != Term("f", X)


def test_intersection():

    x = term('X')
    y = term('f(_)')

    z1 = intersect(x, y)
    z2 = intersect(y, x)

    assert same(z1, z2) and covers(x, z1) and covers(x, z2) and covers(y, z1) and covers(y, z2)

    x = term('X')
    y = term('Y')

    z1 = intersect(x, y)
    z2 = intersect(y, x)

    assert same(z1, z2) and covers(x, z1) and covers(x, z2) and covers(y, z1) and covers(y, z2)

    _,x,y = term('tmp(f(X,Y),f(Y,X))')

    z1 = intersect(x, y)
    z2 = intersect(y, x)

    assert same(z1, z2) and covers(x, z1) and covers(x, z2) and covers(y, z1) and covers(y, z2)


def test_covers():

    assert same(term('X'), term('Y'))
    assert same(term('f(X,Y)'), term('f(A,B)'))
    assert covers(term('f(X,Y)'), term('f(A,A)'))
    assert not covers(term('f(X,X)'), term('f(A,B)'))

    def test(x, y, equals=False, none=False):
        # Note: we parse the terms together so that variables may be shared.
        [_, x, y] = term(f'wrapper({x}, {y})')
        print(f'covers {str(x):10s} {str(y):10s}', end=' ')

        a = covers(x, y)
        b = covers(y, x)   # pylint: disable=W1114

        if term_.OCCURS_CHECK_ENABLED:
            # generalizer must cover both terms (it always exists)
            z = generalizer(x, y)
            print('======>', z, end=' ')
            assert covers(z, x) and covers(z, y)
            if not none:
                # generalizer will equal the more general term. In this test case,
                # we assume that the more general term is `x` unless `none=True`.
                # If we have `equals=True`, then the tie for the "most general term"
                # is broken in favor of `x`.
                assert generalizer(x, y) == x
            else:
                # Neither term is the most general.
                assert z != x and z != y, [x, y, z]

        ok = True
        if a and b:
            ok = equals
        elif a and not b:
            ok = True
        elif not a and b:
            ok = False
        else: # not a and not b:
            ok = none

        if ok:
            print(colors.light.green % 'pass', [a, b])
        else:
            print(colors.light.red % 'fail', [a, b])
        assert ok


    # Very basic:
    test('_', '3')
    test('_', 'f(_)')
    test('_', 'f(1)')

    test('f(_)', 'f(1)')
    test('f(_)', 'f(2)')
    test('f(_)', 'f(_)', equals=True)
    test('f(_)', 'g(_)', none=True)

    test('f(1)', 'f(1)', equals=True)
    test('f(1)', 'f(2)', none=True)
    test('f(f(_))', 'f(1)', none=True)

    test('f(_,_)', 'f(_,_)', equals=True)
    test('f(_,_)', 'f(_,4)')
    test('f(_,_)', 'f(3,_)')
    test('f(_,_)', 'f(3,4)')
    test('f(1,1)', 'f(2,2)', none=True)

    test('f(0,K)', 'f(0,1)')

    test('f(X,4)', 'f(3,Y)', none=True)
    test('f(3,Y)', 'f(X,4)', none=True)

    # Basic cases of nested terms: True
    test('f(X)', 'f(g(Y))')
    test('f(q(X))', 'g(p(X))', none=True)
    test('f(X)', 'f(g(Y))')

    test('f(A, B)', 'f(C, g(D))')

    # Complex term case:
    test('f(A, g(X, B),    Z)',
         'f(C, g(1, B), h(Y))')

    test('f(g(X),    Y)',
         'f(   U, g(V))', none=True)

    # nonlinear example
    test('f(X, X)', 'f(Y, Y)', equals=True)
    test('f(Y, Y)', 'f(X, g(X))', none=True)

    test('f(_,_)', 'f(g(X), g(X))')
    test('f(Y,Y)', 'f(g(X), g(X))')
    test('f(g(X), g(X))', 'f(g(Y), g(Y))', equals=True)

    # nonlinear subset
    test('f(_, _)', 'f(X, X)')
    test('f(Y,Y)', 'f(g(X), g(X))')
    test('f(g(_), g(_))', 'f(g(X), g(X))')

    test('h(f(_, _))', 'h(f(X, X))')
    test('f(h(_), h(_))', 'f(h(X), h(X))')

    # occurs check cases

    with setunset(term_, 'OCCURS_CHECK_ENABLED', True):
        test('f(X)', 'f(f(X))', none=True)
        test('X', 'f(X)', none=True)
        test('f(X)', 'f(X)', equals=True)    # equal, despite the occurs check
#        test('f(X,Y)', 'f(Y,X)', none=True)    # Not equal with the occurs check.

    with setunset(term_, 'OCCURS_CHECK_ENABLED', False):
        test('f(X)', 'f(f(X))', equals=False)
        test('X', 'f(X)', none=True)
        test('f(X)', 'f(X)', equals=True)    # equal, despite the occurs check
        test('f(X,Y)', 'f(Y,X)', equals=True)    # Not equal with the occurs check.

    W,X,Y,Z = map(Var, 'WXYZ')
    for _ in unify(X, Y):
        for _ in unify(Y, Z):
            assert covers(X, 9)
            assert covers(Term('f', X), Term('f', Z))
            assert covers(Term('f', X, Y), Term('f', Y, Z))

        assert covers(Term('f', Y, Y), Term('f', X, Y)), [Term('f', Y, Y), Term('f', W, Z)]
        assert covers(Term('f', Y, Y), Term('f', X, Y)), [Term('f', Y, Y), Term('f', Y, Z)]
        assert covers(Term('f', Y, Z), Term('f', X, Y)), [Term('f', X, Y), Term('f', Y, Z)]


def test_is_ground():
    x = term('s([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])')
    assert is_ground(x)
    x = term('s([1, 1, 1, 1, X, 1, 1, 1, 1, 1, 1])')
    assert not is_ground(x)


def test_canonicalize():
    x = term('s([1,1,1,1,X,1,1,1,1,1,1])')
    have = str(canonicalize(x))
    assert have == 's([1,1,1,1,$X0,1,1,1,1,1,1])', have

    x = term('f(X, X)')
    assert str(canonicalize(x)) == 'f($X0,$X0)'

    x = term('f(X, g(h(X)))')
    have = str(canonicalize(x))
    assert have == 'f($X0,g(h($X0)))'

    Y = Var('Y')
    for _ in unify(Y, 3):
        for _ in unify(x.args[0], Y):
            print(x)
            z = canonicalize(x)
            print(z)
            zz = canonicalize(deref(x))
            print(zz)
            assert str(z) == 'f(3,g(h(3)))', z

    Y = Var('Y')
    for _ in unify(x.args[0], Y):
        have = str(canonicalize(x))
        assert have == 'f($X0,g(h($X0)))'


def test_hash_and_eq():
    X = Var('X')
    Y = Var('Y')

    true = [
        (term('1'), 1),
        (term('f'), term('f()')),
        (Term('f', X), Term('f', X)),
    ]

    false = [
        (term('1'), 2),
        (term('f'), 'f'),     # string does not equal term
        (Term('f', X), Term('f', Y)),
        (term('f(_)'), term('f(_)')),
    ]

    for a,b in true:
        print(a, b)
        assert hash(a) == hash(b)
        assert a == b

    for a,b in false:
        print(a, b)
        assert a != b
        assert hash(a) != hash(b)   # might fail

    x, y = Term('f', X), Term('f', Y)
    assert unifies(x, y)
    for _ in unify(x, y):
        print(x, y)
        assert hash(x) == hash(y)
        assert x == y

    Z = Var('Z')
    x, y = Term('f', X, 3), Term('f', Y, Z)
    assert unifies(x, y)
    for _ in unify(x, y):
        print(x, y)
        assert hash(x) == hash(y)
        assert x == y


def test_pretty_print():

    def test(x, expect=None):
        got = pp(term(x), color=False)
        expect = x if expect is None else expect
        if expect == got:
            print(colors.light.green % 'pass', expect,
                  colors.light.green % '  ==  ', got)
        else:
            print(colors.light.red % 'fail', expect,
                  colors.light.red % '  !=  ', got)
        assert expect == got

    test('"Hello, world."')
    test('1')
    test('3.1415')

    test('[]')
    test('[1,2,3]')
    test('[1,[2],[]]', '[1,[2],[]]')
    test('[1 | X]', '[1|X]')
    test('["hello","world"]')

    test('f([g("hello"),Y])')

    test("'hello word'(X)")
    test("g('f#*&'(X))")
    test("f'(X')")

    # special cases for `$term`.
    test('f(X)', 'f(X)')
    test('a()', 'a')
    #test('F(X)', 'F(X)')

    test('1+2*3', '1 + 2 * 3')
    test('(1+2)*3', '(1 + 2) * 3')

    test('1+2*3', '1 + 2 * 3')          # no parens needed because * is higher priority than +
    test('(1+2)*-3', '(1 + 2) * -3')    # test the opposite case here.

    test('f(X+1), (g(3*exp(X+5)); h(X))', 'f(X + 1), (g(3 * exp(X + 5)); h(X))')

    # Associativity
    test('1+2+3+4', '1 + 2 + 3 + 4')

    # The example below is kind of funny because + is associative, but we get
    # parens in the example because it deviates from the left-assoc declaration
    # in the parser.
    test('1+2+(3+4)', '1 + 2 + (3 + 4)')

    test('((Y = 4), (G = 4), (H is F * G))', 'Y = 4, G = 4, H is F * G')

    # Test that distinct variables with the same name print differently
    X1 = Var('X')
    X2 = Var('X')
    X3 = Var('X')
    got = str(pp(Term('dups', X1, Term('foo', X2, X3))))
    assert got == 'dups(X,foo($X1,$X2))', got

    test('?((Y = 4), ?(G = 4), ?(foo(X)), (H is -F * G))', '?(Y = 4, ?(G = 4), ?foo(X), H is (-F) * G)')

    test('(Y < 4) * 4 + 1 <= 3')

    test(r'(S / H) \ (C / D)', r'S / H \ (C / D)')
    test(r'((S / H) \ C) / D', r'S / H \ C / D')
    test(r'((S / H) \ C) / D', r'S / H \ C / D')

    p = PrettyPrinter()
    assert p([]) == '[]'
    x = term('f(X)')
    assert p([x, x]) == '[f(X), f(X)]'


def test_exception_handling_during_unification():
    from dyna.exceptions import OverBudget

    x = term('f(X, Y)')
    y = term('f(3, Z)')
    z = term('f(W, 4)')

    before = f'{x}; {y}; {z}'
    print(before)

    for _ in unify(x, y):
        print(x, y)

    after = f'{x}; {y}; {z}'
    print(after)
    assert before == after

    from arsenal import assert_throws
    with assert_throws(OverBudget):
        for _ in unify(x, y):
            for _ in unify(y, z):
                print(x, y)
                raise OverBudget

    after = f'{x}; {y}; {z}'
    print(after)
    assert before == after


def test_pickle():
    import pickle
    filename = '/tmp/foo'

    x = term('f(X, g(3, Y))')

    pickle.dump(x, open(filename, 'wb'))
    y = pickle.load(open(filename, 'rb'))
    assert same(x, y)

    import copy
    y = copy.deepcopy(x)
    assert same(x, y)

    y = copy.copy(x)
    assert same(x, y)


def test_gen_functor():
    gen_functor.reset()
    assert gen_functor() == '$gen1'
    assert gen_functor() == '$gen2'
    gen_functor.reset()
    assert gen_functor() == '$gen1'


def test_parser():

    x = term('-3')
    assert x == -3

    x = term('+3')
    assert x == +3

    x = term('"three"')
    assert x == 'three'

    x = term('true')
    assert x is True

    x = term('false')
    assert x is False

    x = term('3.1415')
    assert x == 3.1415

    x = term('-3.1415')
    assert x == -3.1415

    x = term('+3.1415')
    assert x == +3.1415

    x = term('f(*,!,?)')
    assert str(x) == 'f(*,!,?)'

    x = term('A*B+C*D')
    assert str(x) == 'A * B + C * D'

    x = term('A*(B+C)')
    assert str(x) == 'A * (B + C)'

    x = 'A ~> B ~> C'
    y = str(term(x))
    assert y == x, [x, y]

    x = '(A ~> B) ~> C'
    y = str(term(x))
    assert y == x, [x, y]

    PrettyPrinter().print(term('x+y'), '')


if __name__ == '__main__':
    from arsenal.testing_framework import testing_framework
    testing_framework(globals())
