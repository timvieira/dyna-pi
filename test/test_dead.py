"""
Test cases for dead and useless rule elimination
"""

from dyna import Program


def test_useful():
    p = Program("""

    goal += 1 * a(I,I).
    a(I,K) += b(I,J) * c(J,K).

    inputs: b(_,_); c(_,_).
    outputs: goal.

    """)

    q = p._useful()
    #print(q)

    q.assert_equal("""
    goal += a(I,I).
    a(I,K) += b(I,J) * c(J,K).

    $useful(goal) += goal.
    $useful(a(I,I)) += $useful(goal) * a(I,I).
    $useful(b(I,J)) += $useful(a(I,K)) * b(I,J) * c(J,K).
    $useful(c(J,K)) += $useful(a(I,K)) * b(I,J) * c(J,K).
    """)

    q.type_analysis().assert_equal("""
    b(I,K) :- $bound(I), $bound(K).
    c(I,K) :- $bound(I), $bound(K).
    a(I,K) :- $bound(I), $bound(K).
    goal.
    $useful(goal).
    $useful(a(I,I)) :- $bound(I).
    $useful(b(I,J)) :- $bound(I), $bound(J).
    $useful(c(J,I)) :- $bound(I), $bound(J).
    """)

    p.prune().assert_equal("""
    goal += a(I,I).
    a(K,K) += b(K,J) * c(J,K).
    """)


#def test_cky0():
#    from dyna.benchmarks.cky import CKY0
#
#    b = CKY0()
#    p = b.src
#    b(p, 1)
#
#    q = p.prune()
#    b(q, 1)


def test_cky_less():

    p0 = Program("""
    phrase(X,I,K) += rewrite(X,Y,Z) * phrase(Y,I,J) * phrase(Z,J,K).
    phrase(X,I,K) += rewrite(X,Y) * phrase(Y,I,K).
    phrase(X,I,K) += rewrite(X,Y) * word(Y,I,K).
    goal(N) += phrase("ROOT", 0, N) * (N < 10).

    inputs: word(X,I,K); rewrite(X,Y,Z); rewrite(X,Y); rewrite(X,Y).
    outputs: goal(N).
    """)

    p = p0._useful()

    input_type = Program("""

    word(X,I,K) :- w(X), n(I), n(K), (I < K).
    rewrite(X,Y,Z) :- k(X), k(Y), k(Z).
    rewrite(X,Y) :- k(X), k(Y).
    rewrite(X,Y) :- k(X), w(Y).

    """, 'k(_). n(_). w(_). (_ < _).', '')

    rewrites = """
    k("ROOT").
    $fail :- k(X), w(X).
    $fail :- k(X), n(X).
    n(0).
    (I < K) :- (I < J), (J < K).
    $fail :- (I < J), (J < I).
    $fail :- (I < I).
    """

    s = p.type_analysis(input_type, rewrites)
    #print(s)

    # top-down version knows that phrase(X,I,K) has I>=0... not super useful, but interesting
    #s0 = p0.type_analysis(input_type, rewrites)
    #s.chart.compare(s0.chart)

    # Warning: user query here is simple type intersection, so the *head* also
    # drives these query - unlike user_query against a program.  In other words,
    # s.usery_query is not the same s.chart.user_query
    #t = s.intersect('$both(X).')

    # TODO: this chart is a little more fragmented than I would like -- there is
    # a lot of special handling for 0

    s.assert_equal("""
    $useful(goal(N)) += (0 < N) * (N < 10) * n(N).
    $useful(phrase(Y,0,J)) += n(J) * k(Y) * (0 < J) * (J < 10).
    $useful(phrase(Y,I,J)) += (0 < I) * n(I) * (I < J) * (J < 10) * (I < 10) * k(Y) * (0 < J) * n(J).
    $useful(rewrite(X,Y,Z)) += k(Y) * k(Z) * k(X).
    $useful(rewrite(X,Y)) += k(X) * k(Y).
    $useful(rewrite(X,Y)) += k(X) * w(Y).
    $useful(word(Y,0,K)) += (0 < K) * (K < 10) * w(Y) * n(K).
    $useful(word(Y,I,K)) += (I < K) * (0 < I) * (I < 10) * (0 < K) * w(Y) * n(K) * n(I) * (K < 10).

    goal(N) += (0 < N) * (N < 10) * n(N).
    phrase(X,I,K) += n(I) * k(X) * n(K) * (I < K).

    rewrite(X,Y,Z) += k(Z) * k(Y) * k(X).
    rewrite(X,Y) += k(Y) * k(X).
    rewrite(X,Y) += k(X) * w(Y).
    word(X,I,K) += w(X) * (I < K) * n(K) * n(I).

    """)


def test_geom():

    p = Program("""
    x += b.
    x += a*x.

    x += impossible.

    goal += x.

    % possible, but not useful items
    y += d.
    y += c*y.

    inputs: a; b; c; d.
    outputs: goal.
    """)

    u = p._useful()
    #print(u)

    m = u.type_analysis()
    m.chart.user_lookup('$useful(_)').assert_equal("""
    $useful(goal).
    $useful(x).
    $useful(b).
    $useful(a).
    """)

    p.prune().assert_equal("""

    x += b.
    x += a*x.

    goal += x.

    """)

    p.prune_bottom_up().assert_equal("""

    x += b.
    x += a*x.

    goal += x.

    y += d.
    y += c*y.

    """)

    p.prune_fast().assert_equal("""
    x += b.
    x += a*x.

    goal += x.

    """)


def test_simple1():
    p = Program("""

    % this is the core program
    b(1) += c(1).
    b(X) += c(X).
    a(X) += b(X).
    goal(X) += a(X).

    % gets built, but doesn't feed into goal
    f(X) += c(X).
    g(X) += f(X).
    g(X) += misc * 0.

    % feeds into goal, but never gets built
    goal(X) += d(X).
    goal(X) += a(X) * cantbuild(X).  % a(X) subgoal is built, but not the other one

    """, 'c(Y).', 'goal(X).')


    have = p.prune_bottom_up()
    have.assert_equal("""
    a(X) += b(X).
    b(1) += c(1).
    b(X) += c(X).
    f(X) += c(X).
    g(X) += f(X).
    goal(X) += a(X).
    """)

    have = p.prune()
    have.assert_equal("""
    a(X) += b(X).
    b(1) += c(1).
    b(X) += c(X).
    goal(X) += a(X).
    """)

    have = p.prune()
    have.assert_equal("""
    a(X) += b(X).
    b(1) += c(1).
    b(X) += c(X).
    goal(X) += a(X).
    """)


def test_simple2():
    p = Program("""
    f(X) += 1.
    f(X) += g(X) * h(X).  % dead
    goal += f(X).         % alive thanks to first rule
    goal += k(X).

    inputs: g(X); k(X).   % missing h(X).
    outputs: goal.
    """)
    q = p.prune()
    q.assert_equal("""
    f(X) += 1.
    goal += f(X).
    goal += k(X).
    """)


def test_equality_chain():

    p = Program("""
    goal += g(X1,X2) * g(X2,X3) * g(X3,X4).   % chain of equalities
    g(X,X) += h(X).

    foo += g(2,3).   % dead: args of g are always equal
    foo += g(5,5).

    """, 'h(X).', 'goal.')

    p.prune_bottom_up(specialize=False).assert_equal("""
    goal += g(X1,X2) * g(X2,X3) * g(X3,X4).
    g(X,X) += h(X).
    foo += g(5,5).
    """)

    p.prune_bottom_up(specialize=True).assert_equal("""
    goal += g(X,X) * g(X,X) * g(X,X).
    g(X,X) += h(X).
    foo += g(5,5).
    """)

    p.prune(specialize=True).assert_equal("""
    goal += g(X,X) * g(X,X) * g(X,X).
    g(X,X) += h(X).
    """)

    p.prune(specialize=False).assert_equal("""
    goal += g(X1,X2) * g(X2,X3) * g(X3,X4).
    g(X,X) += h(X).
    """)


if __name__ == '__main__':
    from arsenal.testing_framework import testing_framework
    testing_framework(globals())
