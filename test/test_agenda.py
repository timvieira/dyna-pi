"""
Implementation the semi-naive update operator
"""
import numpy as np
from dyna import Program


def test_slow_catalan():
    p = Program("""
    x += 0.5.
    x += 0.5*x*x.

    outputs: x.
    """)

    sol = p.binarize().agenda()
    sol.assert_equal_query('x', 1, precision=2)

    sol = p.agenda()
    sol.assert_equal_query('x', 1, precision=2)


def test_boolean_catalan():
    from semirings import Boolean

    p = Program("""
    x.
    x += x*x.

    outputs: x.
    """, semiring=Boolean)

    sol = p.booleanize().agenda()
    sol.assert_equal_query('x', Boolean.one)


def test_geom1():
    p = Program("""
    x += 1.
    x += 0.5 * x.

    outputs: x.

    """)

    have = p.agenda()
    want = p().sol()
    have.assert_equal(want)


def test_geom2():
    p = Program("""
    x(I) += 1.
    x(I) += 0.5 * x(I).

    outputs: x(I).
    """)

    have = p.agenda()
    have.assert_equal('x(I) += 2.')
    #want = p.fc()
    #have.assert_equal(want)


def test_geom3():
    p = Program("""
    x(I,J) += 1.
    x(I,J) += 0.5 * x(I,J) * (I < J).

    outputs: x(I,J).
    """)

    have = p.agenda()
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

    have = p.agenda()
    want = p().sol()
    have.assert_equal(want)


#def test_cky():
#    from dyna.benchmarks.cky import CKY, PAPA_DATA
#    p = CKY().src + PAPA_DATA
#    want = p.fc()
#    have = p.agenda()
#    have.assert_equal(want)


def test_catalan():

    p = Program("""
    x += .1.
    x += x * x.

    outputs: x.

    """)

    have = p.agenda()
    want = p.fc()
    have.assert_equal(want)


def test_infinite_multiplicity():
    p = Program("""

    goal += f(X).

    f(1) += 2.
    f(X) += 3.

    g(X) += f(X) * 4.

    outputs: goal.

    """)

    have = p.agenda()
    want = p.fc()
    have.assert_equal(want)


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


    d = p.agenda()

    d.user_lookup('goal').assert_equal("""
    goal += 2.
    """)

    #a = np.array([
    #    [1,2],
    #    [3,4],
    #])

    #print(a @ a)

    d.user_lookup('b(I,K)').assert_equal("""
    b(0, 0) += 7.
    b(1, 0) += 15.
    b(0, 1) += 10.
    b(1, 1) += 22.
    """)


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
