import numpy as np
import pytest

from dyna import Program


# Most programs in this file converge under both bounding strategies —
# magic prunes more aggressively but the bare Boolean SCC pass also
# terminates. Parametrizing over both checks the unified `scc_solver`
# path against each.
@pytest.fixture(params=[False, True], ids=['no-magic', 'magic'])
def magic(request):
    return request.param


def test_geoms(magic):

    p = Program("""
    a += 1.
    a += a * 0.5.
    """, '', 'a.')

    p.scc_solver(magic=magic).user_query('a').assert_equal("""
    a += 2.
    """, precision=3)

    p = Program("""
    a(X) += 1.
    a(X) += a(X) * 0.5.
    """, '', 'a(_).')

    d = p.scc_solver(solver=2, magic=magic)
    d.user_query('a(X)').assert_equal("""
    a(X) += 2.
    """, precision=3)

    d.user_query('a("meow")').assert_equal("""
    a("meow") += 2.
    """, precision=3)


def test_nonground_basics(magic):

    p = Program("""
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
    """, '', 'goal.')

    d = p.scc_solver(solver=2, magic=magic)

    def f(X, Y):
        f = 1
        if X == 3: f += 2
        if Y == 4: f += 3
        if X == 3 and Y == 4: f += 4
        return f

    goal = sum(f(I, J) for I in (3, 4) for J in (3, 4, 5))

    d.user_query('goal').assert_equal(f"""
    goal += {goal}.
    """)


def test_nonlinear(magic):
    # Nonlinear body (`a(I,J) * a(J,K)`) exercises `linearize()`. This
    # was a regression: `scc_solver(solver=2)` used to double-linearize,
    # giving `$gen*` names that didn't match between passes, so the
    # priority filter pruned every `b(_,_)` update. Now both passes
    # share one linearization.

    p = Program("""
    g(3).
    g(4).

    goal += g(I) * g(I).

    a(0,0) += 1.
    a(0,1) += 2.
    a(1,0) += 3.
    a(1,1) += 4.

    b(I,K) += a(I,J) * a(J,K).
    """, '', 'goal. b(_,_).')

    d = p.scc_solver(solver=2, magic=magic)

    d.user_query('goal').assert_equal("""
    goal += 2.
    """)

    a = np.array([[1, 2], [3, 4]])
    aa = a @ a
    d.user_query('b(I,K)').assert_equal(f"""
    b(0, 0) += {aa[0, 0]}.
    b(0, 1) += {aa[0, 1]}.
    b(1, 0) += {aa[1, 0]}.
    b(1, 1) += {aa[1, 1]}.
    """)


def test_infinite_diagonal(magic):
    # In Boolean, only the diagonal `g(X,X)` is true, so even bare
    # bounding terminates on `goal(X,X)`. Both passes should agree.
    p = Program("""
    goal(X1,X4) += g(X1,X2) * g(X2,X3) * g(X3,X4).
    g(X,X) += 2.
    """, '', 'goal(_,_).')

    p.scc_solver(solver=2, magic=magic).user_query('goal(X,X)').assert_equal("""
    goal(X, X) += 8.
    """)


def test_builtins(magic):

    p = Program("""
    f(0).
    f(Y) += f(X), Y is X+1, X < 5.
    """, '', 'f(_).')

    p.scc_solver(solver=2, magic=magic).user_query('f(_)').assert_equal("""
    f(0) += 1.
    f(1) += 1.
    f(2) += 1.
    f(3) += 1.
    f(4) += 1.
    f(5) += 1.
    """)


def test_small_cky(magic):
    # Ambiguous grammar — `goal` equals the number of parse trees, so
    # the assertion catches both under- and over-derivation.

    p = Program("""
    phrase(X,I,K) += rewrite(X,Y,Z) * phrase(Y,I,J) * phrase(Z,J,K).
    phrase(X,I,K) += rewrite(X,Y) * word(Y,I,K).
    goal += phrase("ROOT", 0, N) * length(N).

    word("a", 0, 1) += 1.
    word("b", 1, 2) += 1.
    length(2) += 1.

    rewrite("ROOT", "A", "B") += 1.
    rewrite("ROOT", "C", "D") += 1.
    rewrite("A", "a") += 1.
    rewrite("B", "b") += 1.
    rewrite("C", "a") += 1.
    rewrite("D", "b") += 1.
    """, '', 'goal.')

    p.scc_solver(solver=2, magic=magic).user_query('goal').assert_equal("""
    goal += 2.
    """)


def test_data_arg(magic):
    # `data` is added to the program for both passes; supports a string
    # or a Program.
    p = Program("""
    goal += f(X).
    """, 'f(X).', 'goal.')

    d = p.scc_solver(solver=2, magic=magic, data="""
    f(1) += 2.
    f(2) += 3.
    """)
    d.user_query('goal').assert_equal("""
    goal += 5.
    """)

    d2 = p.scc_solver(solver=2, magic=magic, data=Program("""
    f(1) += 2.
    f(2) += 3.
    """))
    d2.user_query('goal').assert_equal("""
    goal += 5.
    """)


# ----------------------------------------------------------------------
# Stress tests: programs where magic-bounding is *necessary* for
# pass-1 termination. These are deliberately not parametrized — the
# `magic=False` variant would diverge.
# ----------------------------------------------------------------------

def test_ground_term_growth_needs_magic():
    # Bare Boolean pass diverges (each iteration mints `f(g^n(0))` for
    # n=0,1,2,...). Magic templates seed `$magic(goal)`, which demands
    # only the specific instance `f(g(g(g(0))))` and propagates that
    # specific demand down the recursion — finite chart.

    p = Program("""
    f(0).
    f(g(X)) += f(X).
    goal += f(g(g(g(0)))).
    """, '', 'goal.')

    d = p.scc_solver(solver=2, magic=True)
    assert not d.pass1_interrupted, 'magic should bound pass-1 to fixpoint'
    d.user_query('goal').assert_equal("""
    goal += 1.
    """)

    # The bare bounding pass diverges — pass-1 must be budget-truncated.
    d_bare = p.scc_solver(solver=2, magic=False, budget=.2)
    assert d_bare.pass1_interrupted, 'bare Boolean pass should diverge'


def test_path_query_finite_with_magic():
    # Transitive closure on a small chain, queried for a specific source
    # node. Without magic, `path(X, Y)` is computed for all reachable
    # pairs. With magic seeded from `goal`, demand propagates
    # `path("a", _)` and the chart stays focused.

    p = Program("""
    edge("a", "b") += 1.
    edge("b", "c") += 1.
    edge("c", "d") += 1.

    path(X, Y) += edge(X, Y).
    path(X, Y) += edge(X, Z) * path(Z, Y).

    goal += path("a", "d").
    """, '', 'goal.')

    d = p.scc_solver(solver=2, magic=True)
    d.user_query('goal').assert_equal("""
    goal += 1.
    """)


def test_bodied_output_seed_unification():
    # A bodied output `goal(X) :- X = 5` should restrict the magic seed
    # to that single binding, so only `goal(5)` enters the chart even
    # though `goal(3)` and `goal(7)` are ground facts in the program.

    outputs = Program('goal(X) :- X = 5.')
    p = Program("""
    goal(3) += 1.
    goal(5) += 1.
    goal(7) += 1.
    """, '', outputs)

    d = p.scc_solver(solver=2, magic=True)
    d.user_query('goal(_)').assert_equal("""
    goal(5) += 1.
    """)


def test_bodied_output_seed_input_binder():
    # Bodied output `goal(X) :- want(X)` with `want` declared as input —
    # the seed body is range-restricted by the input data, so only the
    # demanded `goal(_)` items are computed. This is the canonical use
    # case: client-specified queries (`want`) filter what gets derived.

    outputs = Program('goal(X) :- want(X).')
    p = Program("""
    goal(0) += 1.
    goal(1) += 1.
    goal(2) += 1.
    goal(3) += 1.
    goal(4) += 1.
    inputs: want(_).
    """, '', outputs)

    d = p.scc_solver(solver=2, magic=True, data='want(1) += 1. want(3) += 1.')
    d.user_query('goal(_)').assert_equal("""
    goal(1) += 1.
    goal(3) += 1.
    """)


def test_bodied_output_finite_range():
    # Bodied output `goal(X) :- myrange(X)` with `myrange` declared
    # input restricts demand to the finite client-supplied range.
    # Items in `h` outside that range (15, 20) are never demanded and
    # so never enter the chart.

    outputs = Program('goal(X) :- myrange(X).')
    p = Program("""
    h(0) += 1.
    h(5) += 1.
    h(10) += 1.
    h(15) += 1.
    h(20) += 1.
    goal(X) += h(X).   % Note: h(X) is intentionally dead

    """, 'myrange(X).', outputs)

    d = p.scc_solver(solver=2, magic=True,
                     data='myrange(0) += 1. myrange(5) += 1. myrange(10) += 1.')
    d.user_query('goal(_)').assert_equal("""
    goal(0) += 1.
    goal(5) += 1.
    goal(10) += 1.
    """)
    # h(15), h(20) should NOT be in the chart — their demand was pruned.
    d.user_query('h(_)').assert_equal("""
    h(0) += 1.
    h(5) += 1.
    h(10) += 1.
    """)


def test_bodied_output_seed_structurally_preserved():
    # Structural check: the body of an output declaration appears
    # verbatim in the magic seed rule (modulo SIPS reordering).

    outputs = Program('goal(X) :- want(X).')
    p = Program("goal(X) += 1.", 'want(_).', outputs)
    mt = p.magic_templates()

    [seed] = [r for r in mt.rules
              if isinstance(r.head, type(p.outputs.rules[0].head))
              and r.head.fn == mt.magic_fn
              and r.head.args[0].fn == 'goal']
    assert any(b.fn == 'want' for b in seed.body), \
        f'output body atom should appear in magic seed; got {list(seed.body)}'


if __name__ == '__main__':
    from arsenal.testing_framework import testing_framework
    testing_framework(globals())
