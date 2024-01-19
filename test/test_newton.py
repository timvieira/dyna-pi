import numpy as np

from dyna import Program, Symbol
from semirings import MinPlus


def test_geom1():
    p = Program("""
    x += 1.
    x += 0.5 * x.

    outputs: x.

    """)

    have = p.newton()

    want = p.sol()

    have.assert_equal(want)


def test_geom_nonground():
    p = Program("""
    x(I) += 1.
    x(I) += 0.5 * x(I).

    outputs: x(I).

    """)

    have = p.newton()

    want = p.fc()

    have.assert_equal(want)


def test_geom_symbol():
    p = Program("""
    x += `b`.
    x += `a` * x.

    outputs: x.

    """, semiring=Symbol)

    have = p.newton()

    #have.assert_equal(want)
    print(have)

    a,b = map(Symbol.lift, 'ab')
    assert len(have) == 1 and have.rules[0].body[0] == a.star() * b


def test_catalan_symbol():

    # this CFG generates the language a*
    p = Program("""
    x.
    x += `a`.
    x += x * x.

    outputs: x.

    """, semiring=Symbol)

    have3 = p.newton(T=3)
    have4 = p.newton(T=4)
    #print(have)
    #print(have4)
    have3.assert_equal(have4)

    have = p.newton()
    #print(have)
    #have.assert_equal(want)

    a = Symbol.lift('a')

    assert have.rules[0].body[0] == a.star()


def test_infinite_multiplicity():
    p = Program("""

    goal += f(X).

    f(1) += 2.
    f(X) += 3.

    g(X) += f(X) * 4.

    outputs: goal.

    """).lift_semiring(MinPlus)

    have = p.newton()
    want = p.fc()
    have.assert_equal(want)


def test_catalan():

    p = Program("""
    x += .1.
    x += x * x.

    outputs: x.

    """)

    have = p.newton()

    #want = p.sol()
    want = p.fc()

    have.assert_equal(want)


def test_catalan_slow():

    p = Program("""
    x += 0.5.
    x += 0.5 * x * x.

    outputs: x.

    """)

    have = p.newton(verbosity=2, fmt=lambda x: x.round(4).__repr__(numbered=0))

    #want = p.sol()
    #want = p.fc()

    have.assert_equal('x += 1.', precision=3)



def test_catalan_nonground():

    p = Program("""
    x(I) += .1.
    x(I) += x(I) * x(I).

    outputs: x(I).

    """)

    have = p.newton()

    want = p.fc()

    have.assert_equal(want)


def test_simple():
    p = Program("""
    x += .21.
    x += x * y * z.
    y += 1 * x.
    z += 1.

    outputs: x.

    """)

    want = p.sol()

    have = p.newton(T=4)   # just to test iteration limit (gives lower precision answer)
    have.assert_equal(want, precision=3)

    have = p.newton()
    have.assert_equal(want)


#def test_cky():
#    from dyna.benchmarks.cky import CKY, PAPA_DATA
#    p = CKY().src + PAPA_DATA
#    want = p.sol()
#    have = p.newton()
#    have.assert_equal(want)


def test_nonlinear():

    p = Program("""

    g(3).
    g(4).

    goal += g(I) * g(I).

    a(0,0) += 1.
    a(0,1) += 2.
    a(1,0) += 3.
    a(1,1) += 4.

    b(I,K) += a(I,J) * a(J,K).

    """)


    d = p.newton()

    d.user_lookup('goal').assert_equal("""
    goal += 2.
    """)

    a = np.array([
        [1,2],
        [3,4],
    ])

    print(a @ a)

    d.user_lookup('b(I,K)').assert_equal("""
    b(0, 0) += 7.
    b(1, 0) += 15.
    b(0, 1) += 10.
    b(1, 1) += 22.
    """)


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
