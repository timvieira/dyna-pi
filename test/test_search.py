from arsenal import colors
from dyna import Program


def test_startpath():

    p = Program("""

    path(I,I).
    path(I,K) += path(I,J) * edge(J,K).

    goal += start(I) * path(I,K) * stop(K).

    outputs: goal.
    inputs: start(_); edge(_,_); stop(_).
    """)

    G = p.optimizer(p_greedy=0.75)
    G.run(1000)

    G.show_search_stats()

    print('optimizing plans...')
    plan = G.optimize_plans().prune()
    print(plan)

    assert plan.degree == 2, plan

    D = """
    edge(a,a) += 0.5.
    start(a) += 1.
    stop(a) += 1.
    """

    (plan + D).newton().assert_equal_query('goal', 2)

    # cover the `to_collection` method.
    print(len(G.to_collection()))


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
