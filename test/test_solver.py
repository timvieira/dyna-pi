from arsenal.robust import Timeout
from arsenal.assertions import assert_throws
from arsenal import timeit

from dyna.execute.solver import Solver
from dyna import Program, MaxTimes, SolverLimitation, InstFault


def test_budgets():

    p = Program("""
    f(0).
    f(s(X)) += f(X). % runs forever
    """)

    with assert_throws(Timeout):
        Solver(p)(budget=.1, throw=1)


def test_limitation():

    p = Program("""
    f(X) += 1.
    """)

    with assert_throws(SolverLimitation):
        Solver(p)()

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


#def test_cky():
#    from dyna.benchmarks.cky import PAPA_SENTENCE, PAPA_GRAMMAR
#
#    W = PAPA_SENTENCE
#    G = PAPA_GRAMMAR
#
#    D = (W + G).lift_semiring(MaxTimes)
#
#    P = Program("""
#    phrase(X, I, K) += rewrite(X, Y, Z) * phrase(Y, I, J) * phrase(Z, J, K).
#    phrase(X, I, K) += rewrite(X, Y) * phrase(Y, I, K).
#    phrase(X, I, K) += rewrite(X, Y) * word(Y, I, K).
#    goal += length(N) * phrase("ROOT", 0, N).
#    """,
#    inputs='word(_,_,_). length(_). rewrite(_,_). rewrite(_,_,_).',
#    outputs='goal.').lift_semiring(MaxTimes)
#
#    #for _ in range(1000):
#
#    with timeit('inference'):
#        d = P(D)
#        d.user_query('goal')#.assert_equal(Program('goal += 1.0.').lift_semiring(MaxTimes))  # max/times
#
#    #print(result)
#
#    #print(d.sol())
#
#    if 0:
#        for fa in d.index:
#            print()
#            print(fa)
#            for mode in d.index[fa]:
#                print(mode, len(d.index[fa][mode]))
#                print(d.index[fa][mode])
#
#    if 0:
#    #if d.stats is not None:
#        #for s in ['pops']:
#        for s in ['query']:
#        #for s in sorted(d.stats):
#            print()
#            print(s)
#            g = d.stats[s]
#            K = None
#            for x in sorted(g, key = lambda x: -g[x])[:K]:
#                print(g[x], x)
#            if K is not None and len(g) > K and K is not None: print(f'showing top {K}')



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


#def todo_repl(): Program().solver().repl()

if __name__ == '__main__':
    from arsenal.testing_framework import testing_framework
    testing_framework(globals())
