from arsenal import colors

from dyna import Program, gen_functor


def test_linearize():
    gen_functor.reset()
    p = Program("""
    f(1) += 1.
    f(2) += 2.
    f(3) += 3.
    goal += f(I) * f(J) * f(K).

    g(X,Y) += p(X,X') * h(X',Y') * q(Y',Y).
    other += g(3,Y) * g(Y,4).      % look non-linear but is actually fine bc subgoals can't overlap!

    mm(I,K) += m(I,J) * m(J,K).    % overlaps on the diagonal

    goal += f(X) * g(X,Y).

    outputs: goal.

    """)

    q = p.linearize()
    q.assert_equal("""
    f(1) += 1.
    f(2) += 2.
    f(3) += 3.
    goal += f(I) * $gen1(J) * $gen2(K).
    g(X, Y) += p(X, X') * h(X', Y') * q(Y', Y).
    other += g(3, Y) * g(Y, 4).

    mm(I,K) += m(I,J) * $gen3(J,K).

    goal += f(X) * g(X,Y).
    $gen1(J) += f(J).
    $gen2(K) += f(K).
    $gen3(J,K) += m(J,K).
    """)

    q = (
        q.linear_rule_elimination(0)
        .linear_rule_elimination(0)
        .linear_rule_elimination(0)
    )

    q.user_query('goal').assert_equal('goal += 216.')

    #print('starting....')
    #program = elim_gen(q, 20, True)
    #print('final....')
    #print(program)
    #print(len(program))
    #assert len(program) == 27
    #program.assert_equal('goal += 216.')


def test_simplest():

    rs = Program("""
    b += 1.
    a += b.
    """, None, None)

    rs = rs.elim(0)
    rs.assert_equal('a += b. a += 1.')

    rs = rs.elim(1)   # eliminate the `a :- b.` rule.
    rs.assert_equal('a += 1.')


def test_recursion():
    # Example from Eisner & Blatz p.19.  This example shows a few things
    # a) rule elimination in the presence of recursion
    # b) changes to the program's semantics from rule elimination.
    src = Program("""
    s += 1.        % <-- eliminate
    s += 0.5 * s.
    r += s.
    """, None, None)
    d = src.solve().assert_equal("""
    r += 2.
    s += 2.
    """, precision=3)

    # Eliminate the first rule s += 1
    have = src.elim(0)
    want = """
    s += 0.5 * s.
    s += 0.5.
    r += s.
    r += 1.
    """
    have.assert_equal(want)
    d = have.solve()
    d.assert_equal_query('r', 2, precision=3)
    d.assert_equal_query('s', 1, precision=3)

    src = Program("""
    s += 1.
    s += 0.5 * s.  % <-- eliminate
    r += s.
    """, None, None)
    want = """
    s += 1.
    s += 0.25 * s.
    r += s.
    r += 0.5 * s.
    """
    have = src.elim(1)
    have.assert_equal(want)
    d = have.solve()
    d.assert_equal_query('r', 2, precision=3)
    d.assert_equal_query('s', 4/3, precision=3)


def test_order1():
    rs = Program("""
    f(1) += 1.      % <-- eliminate
    f(2) += 1.
    goal :- f(X) * g(X).
    """, None, None)

    rs = rs.elim(0)   # eliminate `f(1).`
    rs.assert_equal("""
    f(2) += 1.
    goal +=        g(1).
    goal += f(X) * g(X).
    """)

    rs = rs.elim(0)   # eliminate `f(2).`
    rs.assert_equal("""
    goal +=        g(1).
    goal +=        g(2).
    goal += f(X) * g(X).
    """)


def test_order2():
    gen_functor.reset()

    rs = Program("""
    f(1) += 1.
    f(2) += 1.
    f(3) += 1.
    goal += f(I) * f(J).
    """, 'f(X).', 'goal.')
    rs.solve().assert_equal_query('goal', 9)

    if 0:
        want = Program("""
        f(2) += 1.
        f(3) += 1.
        goal += f(I) * f(J).
        goal +=    1 * f(J).
        goal += f(I) *    1.
        goal +=    1 *    1.
        """)
    else:
        want = Program("""
        f(2) += 1.
        f(3) += 1.
        goal += $gen1(J).
        goal += f(I) * $gen1(J).
        $gen1(1) += 1.
        $gen1(J) += f(J).
        """)

    want.assert_equal_query('goal', 9)

    have = rs.elim(0)
    have.assert_equal(want)
    have.assert_equal_query('goal', 9)

    have.assert_equal(want)


def test_order3():
    gen_functor.reset()

    src = Program("""
    f(1) += 1.
    f(2) += 1.
    f(3) += 1.
    goal += f(I) * f(J) * f(K).
    """, 'f(_).', 'goal.')

    d = src.solve()
    d.assert_equal_query('goal', 27)

    if 0:
        # Manually applied
        want = Program("""
        f(2) += 1.
        f(3) += 1.
        goal += f(I) * f(J) * f(K).
        goal +=    1 * f(J) * f(K).
        goal += f(I) *    1 * f(K).
        goal += f(I) * f(J) *    1.
        goal += f(I) *    1 *    1.
        goal +=    1 * f(J) *    1.
        goal +=    1 *    1 * f(K).
        goal +=    1 *    1 *    1.
        """)
    else:
        want = Program("""
        f(2) += 1.
        f(3) += 1.
        goal += $gen1(J) * $gen2(K).
        goal += f(I) * $gen1(J) * $gen2(K).
        $gen1(1) += 1.
        $gen1(J) += f(J).
        $gen2(1) += 1.
        $gen2(K) += f(K).
        """)

    d = want.solve()
    d.assert_equal_query('goal', 27)

    # automatically applied rule elimination
    have = src.elim(0)
    d = have.solve()
    d.assert_equal_query('goal', 27)
    have.assert_equal(want)


def test_order3a():

    src = Program("""
    f(1) += 1.
    f(2) += 1.
    f(3) += 1.
    goal += f(I) * f(I) * f(K).
    """, 'f(_).', 'goal.')

    src.assert_equal_query('goal', 9)

    # automatically applied rule elimination
    have = src.elim(0)
    have.assert_equal_query('goal', 9)


def test_shortest_path():

    src = Program("""
    f(S) += start(S).
    f(S) += f(S') * w(S, S').
    """)

    have = src.elim(1)
    have.assert_equal("""
    f(S) += start(S).
    f(S) += f(S') * w($S1, S') * w(S, $S1).
    """)

    have = src.elim(0)
    have.assert_equal("""
    f(S) += f(S') * w(S, S').
    f(S) += start($S1) * w(S, $S1).
    """)


def test_misc():
    gen_functor.reset()

    # For example, suppose
    #   s is s(X,X).
    # Then the rule
    #   r(X) += s(X,Y) * t(Y) should be expressed
    # as
    #   r(X) += (µ * t(Y))[s(X,Y)]

    rs = Program("""
    s(X,X) :- foo(X).
    s(X,X) :- goo(X).
    r(X) :- s(X,Y), t(Y).
    """, None, None)

    rs = rs.elim(0)

    rs.assert_equal("""
    s(X, X) :- goo(X).
    r(X) :- s(X, Y), t(Y).
    r(X) :- foo(X), t(X).
    """)

    # while
    #   r(X) min= s(X,Y) * s(X,Y)
    # should be expressed as
    #   r(X) += (µ * µ)[s(X,Y)]

    rs = Program("""
    s(X,X) :- foo(X).
    s(X,X) :- goo(X).
    r(X) += s(X,Y) * s(X,Y).

    outputs: r(X).
    inputs: foo(X); goo(X).

    """)

    rs = rs.elim_p(0)
    rs.assert_equal("""
    s(X,X) += goo(X).
    r(Y) += foo(Y) * $gen1(Y,Y).
    r(Y) += s(Y,Y) * $gen1(Y,Y).
    $gen1(Y,Y) += foo(Y).
    $gen1(Y,Y) += s(Y,Y).
    """)

    # and
    #   r min= 3
    # can be expressed as
    #   r min= 3[s(X,X)].
    # However,
    #  r(X) += s(X,Y) * s(Y,Z)
    # cannot be expressed in the required form at all.
    # We regard µ as a ground term in considering whether Fi is independent of s

    # XXX: As usual, we need to be careful about double-counting the diagonal:
    #   f(I,J) += ...  <=== elim
    #   goal(I,K) += f(I,J) * f(J,K).
    # or simpler:
    #   f(K) += ...   <=== elim
    #   goal += f(I) * f(J).



def test_order2a():
    gen_functor.reset()
    rs = Program("""
    f(1) += 1.
    f(2) += 1.
    f(3) += 1.
    goal += f(I) * f(I).
    """, 'f(_).', 'goal.')

    d = rs.solve()
    d.assert_equal_query('goal', 3)

    have = rs.elim(0)
    have.assert_equal("""
    f(2) += 1.
    f(3) += 1.
    goal += $gen1(1).
    goal += f(I) * $gen1(I).
    $gen1(1) += 1.
    $gen1(I) += f(I).
    """)

    rs.assert_equal_query('goal', 3)


def test_cky2():

    src = Program("""
    rewrite(np,det,n) += 0.5.
    constit(X,I,K) += rewrite(X,Y,Z) * constit(Y,I,J) * constit(Z,J,K).
    """, None, None)

    have = src.linear_rule_elimination(0)

    have.assert_equal("""
    % specialized rule
    constit(np,I,K) += 0.5 * constit(det,I,J) * constit(n,J,K).

    % general rule
    constit(X,I,K) += rewrite(X,Y,Z) * constit(Y,I,J) * constit(Z,J,K).
    """)


def test_cky3():

    # Example from Blatz & Eisner. They say that we can make the following
    # program range restricted by simply eliminating the first rule.
    src = Program("""
    temp(X0,X0) += 1.
    temp(X,X0) += rewrite(X,Y) * temp(Y,X0).
    other(constit(X,I,K)) += rewrite(X,W) * word(W,I,K).
    other(constit(X,I,K)) += rewrite(X,Y,Z) * constit(Y,I,J) * constit(Z,J,K).
    constit(X,I,K) += temp(X,X0)*other(constit(X0,I,K)).
    """, None, None)

    # This appears to check out.
    #print(src.rules[0])
    have = src.linear_rule_elimination(0)
    print(have)

    have.constant_folding().assert_equal("""
    constit(X, I, K) += temp(X, X0) * other(constit(X0, I, K)).
    constit(X0, I, K) += other(constit(X0, I, K)).
    other(constit(X, I, K)) += rewrite(X, W) * word(W, I, K).
    other(constit(X, I, K)) += rewrite(X, Y, Z) * constit(Y, I, J) * constit(Z, J, K).
    temp(X, X0) += rewrite(X, X0).
    temp(X, X0) += rewrite(X, Y) * temp(Y, X0).
    """)


if __name__ == '__main__':
    from arsenal.testing_framework import testing_framework
    testing_framework(globals())
