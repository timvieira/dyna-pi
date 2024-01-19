from dyna import gen_functor, Program, MaxTimes


#def introduce(p, s, j=0):
#    q = p + s
#    t = q[0]             # assumes only one rule was added...
#    q = q.unfold(0, j)   # one level of unfold might not be enough to tie the knot
#
#    # Notice that there is something somewhat tricky going on below. We run
#    # CSE using the original version of the new rule t (even though it was
#    # transformed in the line above and therefore is not longer literally in
#    # the transformed program).  However, because there is still a
#    # semantically equivalent relation in the program, we are still free to
#    # use the CSE rewrite using t or some other (+= product of subgoals)
#    # sub-expression.
#    q = q.cse(t, add=False)
#    return q

def test_div6():

    p = Program("""
    div2(0).
    div2(s(s(X))) += div2(X).

    div3(0).
    div3(s(s(s(X)))) += div3(X).

    div6(X) += div2(X) * div3(X).

    outputs: div6(X).

    """)

    q = (
        p
        .unfold(4,0)
        .unfold(4,0)
        .unfold(4,1)
        .unfold(5,0)
        .unfold(5,1)
        .unfold(5,0)
        .megafolds(p)
        .prune(specialize=0)[-1]
    )

    q.assert_equal("""
    div6(s(s(s(s(s(s(X))))))) += div6(X).
    div6(0).
    """)


def test_path():
    # Starting point
    p = Program("""
    v(S) += start(S).
    v(S') += v(S) * w(S, S').
    goal += v(S) * stop(S).
    """, inputs= 'w(_,_). start(_). stop(_).', outputs = 'goal.')

    # Mess it up the following unfold action
    q = (p
         .unfold(1, 0, defs=p)
         .unfold(3, 0, defs=p)
         .unfold(4, 0, defs=p)
         .unfold(5, 0, defs=p)
    )

    q.assert_equal("""
    v(S) += start(S).
    goal += v(S) * stop(S).
    v(S') += start(S) * w(S,S').
    v(S') += start(S) * w(S,$S1) * w($S1,S').
    v(S') += start(S) * w(S,$S1) * w($S1,$S2) * w($S2,S').
    v(S') += start(S) * w(S,$S1) * w($S1,$S2) * w($S2,$S3) * w($S3,S').
    v(S') += v(S) * w(S,$S1) * w($S1,$S2) * w($S2,$S3) * w($S3,$S4) * w($S4,S').
    """)


    p = Program("""
    goal += start(S') * v(S').
    v(S) += stop(S).
    v(S) += w(S, S') * v(S').
    """, inputs= 'w(_,_). start(_). stop(_).', outputs = 'goal.')

    # Mess it up the following unfold action
    q = (p
         .unfold(2, 1, defs=p)
         .unfold(3, 2, defs=p)
         .unfold(4, 3, defs=p)
    )

    q.assert_equal("""
    goal += start(S') * v(S') .
    v(S) += stop(S).
    v(S) += w(S,S') * stop(S').
    v(S) += w(S,S') * w(S',$S'1) * stop($S'1).
    v(S) += w(S,S') * w(S',$S'1) * w($S'1,$S'2) * stop($S'2).
    v(S) += w(S,S') * w(S',$S'1) * w($S'1,$S'2) * w($S'2,$S'3) * v($S'3).
    """)


def test_unfold_builtin():

    p = Program("""
    f(X,Z) += g(Y) * 2.5 * (X is 1+2) * (Z is X*Y).
    """, '', 'f(X).')

    q = p.unfold(0, 2).constant_folding().unfold(0, 2)

    # the second built-in doesn't run.
    q.assert_equal("""
    f(3,Z) += g(Y) * 2.5 * (Z is 3 * Y).
    """)


def test_unsafe_unfold_elim():

    p = Program("""
    goal += f(X).
    f(X) += 1.
    """)

    p.unfold(0, 0).assert_equal("""
    f(X) += 1.
    goal += ∞.
    """)

    p.elim(1).assert_equal("""
    goal += f(X).
    goal += ∞.
    """)

    # idempotent case doesn't create an exta factor
    have = p.lift_semiring(MaxTimes).elim(1)
    want = Program("""
    goal += f(X).
    goal += 1.
    """).lift_semiring(MaxTimes)
    have.assert_equal(want)

    # no errors in this case
    p = Program("""
    goal += f(1).
    f(X) += 1.
    """)
    p.unfold(0, 0)
    p.elim(1)

    p = Program("""
    goal += f(X) * g(X).
    f(X) += 1.
    g(X) += 1.
    """)
    p.unfold(0, 0)
    p.elim(1)


def test_hook_simplest():
    gen_functor.reset()

    rs = Program("""
    goal :- a(I), b(I,J), c(J).
    goal :- d(J).
    """)

    new_rs = rs.hook(0, [0, 1])

    want = Program("""
    goal :- $gen1(J) * c(J).
    goal :- d(J).
    $gen1(J) :- a(I), b(I, J).
    """)

    new_rs.assert_equal(want)

    unfolded = want.unfold(0, 0)

    unfolded.assert_equal("""
    $gen1(J) :- a(I), b(I, J).
    goal :- a(I), b(I, J), c(J).
    goal :- d(J).
    """)


def test_foo():

    rs = Program("""
    a(1) += b(1).
    a(2) += b(2).
    a(3) += b(3).
    a(4) += b(4).
    a(K) += b(K).

    goal += a(I) * a(I).

    """, 'b(_).', 'goal.')

    print(rs)

    unfolded = rs.unfold(5, 0)
    print(unfolded)

    unfolded.assert_equal("""
    a(1) += b(1).
    a(2) += b(2).
    a(3) += b(3).
    a(4) += b(4).
    a(K) += b(K).

    goal += b(1) * a(1).
    goal += b(2) * a(2).
    goal += b(3) * a(3).
    goal += b(4) * a(4).
    goal += b(K) * a(K).
    """)

    def run(p):
        d = p.solve("""
        b(1) += 1.
        b(2) += 2.
        b(3) += 3.
        b(4) += 4.
        """)
        d.assert_equal_query('goal', sum((2*i)**2 for i in [1,2,3,4]))

    run(rs)
    run(unfolded)


def test_ryan1():
    gen_functor.reset()

    R = Program("""
    a(X) += b(X) * f(X,Y).
    a(Y) += d(Y) * e(Z,Y).

    goal(J) += a(I) * c(I,J).
    """,
        inputs = 'b(_). f(_,_). e(_,_). c(_,_). d(_).',
        outputs = 'goal(_).'
    )

    S = R.unfold(2, 0)

    S.assert_equal("""
    a(X) += b(X) * f(X,Y).   % dead rule
    a(Y) += d(Y) * e(Z,Y).   % dead rule
    goal(J) += b(X) * f(X,Y) * c(X,J).
    goal(J) += d(Y) * e(Z,Y) * c(Y,J).
    """)

    S = S.prune()
    S.assert_equal("""
    goal(J) += b(X) * f(X,Y) * c(X,J).
    goal(J) += d(Y) * e(Z,Y) * c(Y,J).
    """)

    # runtime(P) = runtime(unfold(fold(P)))
    S = S.hook(0, [0, 1])
    S = S.hook(1, [0, 1])
    S.assert_equal("""
    goal(J) += $gen1(I) * c(I,J).
    goal(J) += $gen2(I) * c(I,J).
    $gen1(I) += b(I) * f(I, Y).
    $gen2(I) += d(I) * e(Z, I).
    """)

    # Merging the following rules can be beneficial if the gen1 and gen2 domains
    # overlap.  [ It is also the case that we need this type of operation to get
    # back to something more like the a(X) program. ]
    #
    #   goal(J) += c(I,J) * $gen1(I).
    #   goal(J) += c(I,J) * $gen2(I).
    #
    # I.e., the following rule is more efficient because the I's are
    # consolidated before multiplying with c (we get a max instead of sum)
    #
    #   $gen3(I) += $gen1(I).
    #   $gen3(I) += $gen2(I).
    #   goal(J) += c(I,J) * $gen3(I).


def test_ryan2():

    R = Program("""
    a(1) += b(1).
    a(2) += b(2).
    a(X) += d(X, Y).
    goal += a(I) * c(I).
    """, 'b(_). d(_,_). c(_).', 'goal.')

    S = R.unfold(-1, 0)
    S = S.prune()

    print(S)

    S.assert_equal("""
    goal += b(1) * c(1).
    goal += b(2) * c(2).
    goal += d(I, Y) * c(I).
    """)


def test_ryan3():
    gen_functor.reset()

    R = Program("""
    f(X) += start(X).
    f(Y) += f(X) * w(X, Y).
    goal += f(X) * finish(X).
    """)

    S = R.unfold(1, 0)

    S.assert_equal("""
    f(X) += start(X).
    goal += f(X) * finish(X).
    f(Y) += start(X) * w(X, Y).
    f(Y) += f(X) * w(X, $X1) * w($X1, Y).
    """)

    T = S.hook(3, [0, 1])

    T.assert_equal("""
    f(X) += start(X).
    goal += f(X) * finish(X).
    f(Y) += start(X) * w(X, Y).
    $gen1(X) += f($X1) * w($X1, X).
    f(Y) += $gen1(X) * w(X, Y).
    """)


def test_manual_fold():
    geom = Program("""
    x += b.
    x += x*a.
    """, 'a. b.', 'x.')
    u = geom.unfold(1,0)
    f = u.manual_fold('x += x*a.', 0, [1,2])
    f.assert_equal(geom)
    assert f.safe_by_rev


if __name__ == '__main__':
    from arsenal.testing_framework import testing_framework
    testing_framework(globals())
