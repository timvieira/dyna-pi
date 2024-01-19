import numpy as np
from arsenal import assert_throws

from dyna import Program, SolverLimitation, InstFault
from dyna.execute.solver2 import Solver


def test_limitation():

    p = Program("""
    f(X) += 1.
    """)

    #with assert_throws(SolverLimitation):
    Solver(p)().assert_equal('f(X) += 1.')

    p = Program("""
    f(X) += X.
    """)

    with assert_throws(InstFault):
        Solver(p)()

    p = Program("""
    f(0).
    f(Y) += f(X), Y is X+1, X < 5.
    """)

    Solver(p)().assert_equal("f(0). f(1). f(2). f(3). f(4). f(5).")

    p = Program("""
    f(0).
    f(Y) += X < 5, f(X), Y is X+1.
    """)

    with assert_throws(InstFault):
        Solver(p)()


def test_nonground_basics():

    d = Solver(Program("""
    f(X,Y) += 1.
    f(3,Y) += 2.
    f(X,4) += 3.
    f(3,4) += 4.

    g(3).
    g(4).
    h(3).
    h(4).
    h(5).

    goal += g(I) * f(I,J) * h(J).

    """))

    d.user_query('f(3,3)').assert_equal("""
    f(3,3) += 3.
    """)

    d.user_query('f(4,4)').assert_equal("""
    f(4,4) += 4.
    """)

    d.user_query('f(3,4)').assert_equal("""
    f(3,4) += 10.
    """)

    def f(X,Y):
        f = 0
        # f(X,Y) += 1.
        f += 1
        # f(3,Y) += 2.
        if X == 3: f += 2
        # f(X,4) += 3.
        if Y == 4: f += 3
        # f(3,4) += 4.
        if X == 3 and Y == 4: f += 4
        return f

    goal = 0
    for I in [3,4]:
        for J in [3,4,5]:
            goal += f(I,J)
    #print('goal=', goal)

    d.user_query('goal').assert_equal(f"""
    goal += {goal}.
    """)


def test_geoms():

    d = Solver(Program("""
    a += 1.
    a += a * 0.5.
    """))

    d.user_query('a').assert_equal("""
    a += 2.
    """)

    d = Solver(Program("""
    a(X) += 1.
    a(X) += a(X) * 0.5.
    """))

    d.user_query('a(X)').assert_equal("""
    a(X) += 2.
    """)

    d.user_query('a("meow")').assert_equal("""
    a("meow") += 2.
    """)


def test_nonlinear():

    d = Solver(Program("""

    g(3).
    g(4).

    goal += g(I) * g(I).

    a(0,0) += 1.
    a(0,1) += 2.
    a(1,0) += 3.
    a(1,1) += 4.

    b(I,K) += a(I,J) * a(J,K).

    """))

    d.user_query('goal').assert_equal("""
    goal += 2.
    """)

    a = np.array([
        [1,2],
        [3,4],
    ])

    print(a @ a)

    d.user_query('b(I,K)').assert_equal("""
    b(0, 0) += 7.
    b(1, 0) += 15.
    b(0, 1) += 10.
    b(1, 1) += 22.
    """)


def test_infinite_diagonal():
    # The product of infinite diagonal matrices is an identity matrix who's
    # value is the product of the value on the diagonal.

    p = Program("""
    % chain of equalities
    goal(X1,X4) += g(X1,X2) * g(X2,X3) * g(X3,X4).
    g(X,X) += 2.   % diagonal matrix
    """, '', 'goal(_,_).')

    Solver(p).user_query('goal(X,X)').assert_equal("""
    goal(X, X) += 8.   % 2*2*2
    """)


def test_infinite_aggregation():
    # Simplest test of aggregating a value over an infinite domain.

    p = Program("""
    goal += f(X).
    f(X) += 1.
    """, '', 'goal.')

    # TODO: solver currently fails on this example.  It gets goal += 1.  because
    # it does not yet check for the nonground local variable.

    Solver(p).user_query('goal').assert_equal("""
    goal += ∞.
    """)


def test_unary_speculation():

    data = """
    word("Papa", 0, 1) += 1.
    word("ate", 1, 2) += 1.
    word("the", 2, 3) += 1.
    word("caviar", 3, 4) += 1.
    word("with", 4, 5) += 1.
    word("a", 5, 6) += 1.
    word("spoon", 6, 7) += 1.
    word(".", 7, 8) += 1.
    length(8) += 1.
    rewrite("ROOT", "S", "<.>") += 1.
    rewrite("S", "NP", "VP") += 1.
    rewrite("NP", "Det", "N") += 1.
    rewrite("NP", "NP", "PP") += 1.
    rewrite("VP", "V", "NP") += 1.
    rewrite("VP", "VP", "PP") += 1.
    rewrite("PP", "P", "NP") += 1.
    rewrite("NP", "Papa") += 1.
    rewrite("N", "caviar") += 1.
    rewrite("N", "spoon") += 1.
    rewrite("N", "fork") += 1.
    rewrite("V", "ate") += 1.
    rewrite("P", "with") += 1.
    rewrite("Det", "the") += 1.
    rewrite("Det", "a") += 1.
    rewrite("<.>", ".") += 1.

    % simple unary chain cycle
    rewrite("Det", "V") += .1.
    rewrite("V", "Det") += .1.
    rewrite("V", "N")   += .1.
    rewrite("N", "V")   += .1.
    rewrite("NP", "PP") += .1.
    rewrite("PP", "NP") += .1.
    """
    expect = """
    goal += 2.224.
    """

    if 0:
        data = """
        word("a", I, K).
        length(1).
        rewrite("ROOT", "A") += 1.
        rewrite("A", "a") += 1.
        rewrite("A", "A") += 0.5.
        """
        expect = """
        goal += 2.
        """

    p = Program("""
    phrase(X,I,K) += rewrite(X,Y,Z) * phrase(Y,I,J) * phrase(Z,J,K).
    phrase(X,I,K) += rewrite(X,Y) * phrase(Y,I,K).
    phrase(X,I,K) += rewrite(X,Y) * word(Y,I,K).
    goal += phrase("ROOT", 0, N) * length(N).
    """ + data, '', 'goal.')

    #d1 = p()
    #print(d1)

    p = p.slash("phrase(X',I',K')", positions={1: 1}).prune_bottom_up()

    d = Solver(p)()
    d.user_query('goal').assert_equal(expect, precision=3)


def test_builtins():

    p = Program("""
    f(0).
    f(Z) += f(X), Y is X+1, Y < 5, Y=Z.
    """)

    want = """
    f(0) += 1.0.
    f(1) += 1.0.
    f(2) += 1.0.
    f(3) += 1.0.
    f(4) += 1.0.
    """

    Solver(p)().assert_equal(want)

    p = Program("""
    a += $not_matches("f(X)", f(X)).
    b += $not_matches("f(X)", g(X)), X=3.
    c += $not_matches("f(X)", g(1)).
    d += $not_matches("f(X)", f(1)).
    """)

    Solver(p)().assert_equal("""
    b += 1.
    c += 1.
    """)

    p = Program("""
    e += $not_matches("f(1)", f(X)).
    """)
    with assert_throws(InstFault):
        Solver(p)()


def test_budgets():
    from arsenal.robust import Timeout
    from arsenal.assertions import assert_throws

    p = Program("""
    f(0).
    f(Y) += f(X), Y is X+1.   % runs forever
    """)

    with assert_throws(Timeout):
        p.solver2()(budget=.1, throw=1)


if __name__ == '__main__':
    from arsenal.testing_framework import testing_framework
    testing_framework(globals())
