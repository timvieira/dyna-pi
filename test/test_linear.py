from dyna import Program
from dyna.execute.linear import kleene_linsolve


def test_basics():

    if 0:
        # [2022-11-26 Sat] The following program is not "linear" under a strict
        # definition of each rule has ≤ 1 item in its body.  That said, there is
        # an evaluation order which "eliminates" the subgoals `a` and `b` and
        # then we are only left with the linear cylic program over `x`.
        p = Program("""
        x += b.
        x += a * x.

        a += 0.5.
        b += 1.

        """)

    p = Program("""
    x += 1.
    x += 0.5 * x.
    """)

    kleene_linsolve(p).assert_equal(p.sol())


def test_nonground_geom():
    # Non-ground geometric series
    p = Program("""
    x(I) += 1.
    x(I) += 0.5 * x(I).
    """)

    kleene_linsolve(p).assert_equal(p.sol())


def todo_nonground2():
    p = Program("""
    g(X) += f(X,4).

    f(X,Y) += 2.
    f(X,4) += 3.
    f(3,4) += 5.
    f(3,Y) += 7.

    """)

    kleene_linsolve(p).assert_equal(p.sol())


def todo_infinite_multiplicity():
    p = Program("""
    goal += 2 * f(X).
    f(X) += 3.
    """)

    kleene_linsolve(p).assert_equal(p.sol())


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
