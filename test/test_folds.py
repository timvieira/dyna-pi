from arsenal import timeit

from dyna import Program


def test_path():
    # Starting point
    p = Program("""
    v(S) += start(S).
    v(S') += v(S) * w(S, S').
    goal += v(S) * stop(S).
    """, inputs= 'w(_,_). start(_). stop(_).', outputs = 'goal.')

    # Mess it up the following unfold action
    q = p.unfold(2, 0)

    q.basic_fold('goal += v(S) * stop(S).', 0, [2,3]).assert_equal(p)

    q = Program("""
    v(S) += start(S).
    v(S') += v(S) * w(S,S').
    goal += start(S) * stop(S).
    goal += v(S) * stop(S') * w(S,S').
    """)

    assert p in q.reversible_megafolds()


def test_geom():
    geom = Program("""
    x += b.
    x += x*a.
    """, 'a. b.', 'x.')
    u = geom.unfold(1,0)
    print(u)

    u.basic_fold('x += x*a.', 0, [1,2]).assert_equal(geom)

    assert geom in u.reversible_megafolds()


# [2022-01-20 Thu] we can invert cky0 because we fail to propose a good A+=B*R rule
#def todo_cky0():
#    from dyna.benchmarks.cky import CKY0
#    cky0 = CKY0().src
#    q = cky0.unfold(1, 1)
#
#    # basic fold succeeds at the round trip
#    r = q.basic_fold(cky0.rules[1], 1, q.new2def)
#    r.assert_equal(cky0)
#
#    # Our method for proposing the A+=B*R rule is insufficient because it can't
#    # figure out that we need to generalize away from the variable bindings.
#    #
#    # [2022-03-06 Sun] running megafolds takes FOREVER on this example.
#    #
#    #for p in q.megafolds(q): print(p)


def test_cky3():

    p = Program("""
    phrase(X,I,K) += rewrite(X,Y,Z) * phrase(Y,I,J) * phrase(Z,J,K).
    phrase(X,I,K) += rewrite(X,Y) * phrase(Y,I,K).
    phrase(X,I,K) += rewrite(X,Y) * word(Y,I,K).
    goal += length(N) * phrase("ROOT", 0, N).

    inputs: word(_,_,_); length(_); rewrite(_,_,_); rewrite(_,_).
    outputs: goal.

    """)

    p0 = p

    for qqq in p.reversible_megafolds(p):
        assert False, qqq

    #for qqq in folds(p, p, {PARTIAL}):
    #    print('potentially unsafe folds:', qqq)

    q = p.unfold(0, 1)

    q.basic_fold(p.rules[0], 1, [3,4,5]).assert_equal(p)

    assert p in q.reversible_megafolds()
    print('one: ok')

    p = q
    q = p.unfold(0, 1)

    print(p)
    print(p.degrees())

    # we can't match this one at all
    pp = Program("""
    phrase(X, I, K) += rewrite(X, Y) * phrase(Y, I, K).
    phrase(X, I, K) += word(X, I, K).
    goal += length(N) * phrase("ROOT", 0, N).
    phrase(X, I, K) += rewrite(X, Y, Z) * rewrite(Y, $Y1) * phrase($Y1, I, J) * phrase(Z, J, K).
    phrase(X, I, K) += rewrite(X, Y, Z) * word(Y, I, J) * phrase(Z, J, K).
    phrase(X, I, K) += rewrite(X, Y, Z) * rewrite(Y, $Y1, $Z1) * phrase($Y1, I, J) * phrase($Z1, J, $J1) * rewrite(Z, $Y2) * phrase($Y2, $J1, K).
    phrase(X, I, K) += rewrite(X, Y, Z) * rewrite(Y, $Y1, $Z1) * phrase($Y1, I, J) * phrase($Z1, J, $J1) * word(Z, $J1, K).
    phrase(X, I, K) += rewrite(X, Y, Z) * rewrite(Y, $Y1, $Z1) * phrase($Y1, I, J) * phrase($Z1, J, $J1) * rewrite(Z, $Y2, $Z2) * rewrite($Y2, $Y3, $Z3) * phrase($Y3, $J1, $J2) * phrase($Z3, $J2, $J3) * phrase($Z2, $J3, K).
    phrase(X, I, K) += $gen(Y, Z, I, J) * rewrite(X, Y, $Z1) * phrase(Z, J, $J1) * rewrite($Z1, $Y1, $Z2) * rewrite($Y1, $Y2) * phrase($Y2, $J1, $J2) * phrase($Z2, $J2, K).
    phrase(X, I, K) += rewrite(X, Y, Z) * rewrite(Y, $Y1, $Z1) * phrase($Y1, I, J) * phrase($Z1, J, $J1) * rewrite(Z, $Y2, $Z2) * word($Y2, $J1, $J2) * phrase($Z2, $J2, K).
    $gen(Y, Z, I, J) += rewrite(Y, $Y1, Z) * phrase($Y1, I, J).
    """, p.inputs, p.outputs, p.semiring)
    pp = pp.elim_p(10)
    print('Re-folding program:')
    print(pp)
    print('degrees=')
    print(pp.degrees())


    xxx = Program("""
    goal += length(N) * phrase("ROOT",0,N).
    phrase(X,I,K) += phrase(Y,I,J) * rewrite(X,Y,Z) * phrase(Z,J,K).
    phrase(X,I,K) += rewrite(X,Y) * phrase(Y,I,K).
    phrase(X,I,K) += word(X,I,K).
    """)

    found = False
    with timeit('fold'):
        for qq in pp.reversible_megafolds():
            print()
            print(qq.degrees())
            print(qq)

            for qqq in qq.reversible_megafolds():
                print()
                print(qqq.degrees())
                print(qqq)

                #xxx.compare(qqq)

                found |= (qqq == xxx)

    assert found


def test_multiplicity():

    p = Program("""
    goal += f(X).
    goal += f(Y)*1.
    goal += 3*f(Y).

    m.
    m += 1.
    m += 3.

    inputs: f(_).
    outputs: goal.
    """)

    target = Program("""
    goal += m*f(X).

    m.
    m += 1.
    m += 3.

    inputs: f(_).
    outputs: goal.
    """)

    assert target in p.reversible_megafolds()

    target.constant_folding().elim_p(1).assert_equal("""
    goal += 5 * f(X).
    """)


def test_derivation_map_reversible():
    from dyna import Symbol

    p = Program("""
    x += `b`.
    x += `a` * `b`.
    x += `a` * `a` * x.

    inputs: a; b.
    outputs: x.
    """, semiring=Symbol)

    q = p.basic_fold(r=Program('x += `a` * x.').rules[0], S={1,2}, j=1)

    # Recall that reversible folds have a different safety condition: they
    # unfold wrt the target program rather than an auxiliary program - by
    # default the auxiliary definitions would be the source program.
    assert not q.partially_safe   # this is the special thing
    assert q.undo == p

    #m = RelativeMeasure.from_program_stratified(p)
    #print(m(q))

    q.rev.assert_equal(p)

    p = Program("""
    x += `b`.
    x += `a` * `b`.
    x += `a` * `a` * x.

    inputs: a; b.
    outputs: x.
    """, semiring=Symbol)

    q = p.basic_fold(r=Program('x += `a` * x.').rules[0], S={1,2}, j=1)

    for d in p.derivations(5, 'x'):
        print()
        print(d)
        D = q.transform(d)
        print(D)
        print()


def test_peano_equivalence():

    p = Program("""
    peano(z).
    peano(s(X)) += peano(X).

    giuseppe(z).
    giuseppe(s(X)) += giuseppe(X).

    """)

    q = Program("""
    giuseppe(X) += peano(X).

    peano(z).
    peano(s(X)) += peano(X).

    """)

    # q to p
    pp = q.unfold(0,0).megafolds(q)[1]
    pp.assert_equal(p)

    assert p in q.unfolds().megafolds(q)

    # TODO: can we go from p to q???

    #for new in p.partial_megafolds(p):
    #    print(new)


def test_type():

    p = Program("""

    p([], []) :- list([]).
    p([X|Xs], [f(X)|Xs']) :- list(Xs), p(Xs,Xs').

    q(Xs,Xs') += list(Xs), p(Xs,Xs').

    list([]).
    list([X|Xs]) :- list(Xs).

    outputs: p(_,_).

    """)

    q = p.user_lookup('q(_,_)')
    q1 = q.unfold(0,1,defs=p).unfold(0,1,defs=p).unfold(1,0,defs=p).unfold(0,0,defs=p)

    # drop duplicate constraint
    q1.assert_equal("""
    q([],[]).
    q([X|Xs],[f(X)|Xs']) += list(Xs) * list(Xs) * p(Xs,Xs').
    """)

    # In order to nail this example, we need duplicate constraint elimination.
    # Below, I have done that transform manually :-/
    q1 = Program("""
    q([],[]).
    q([X|Xs],[f(X)|Xs']) += list(Xs) * p(Xs,Xs').
    """)

    q2 = q1.partial_megafolds(p)[1]

    q2.assert_equal("""
    q([X|Xs],[f(X)|Xs']) += q(Xs,Xs').
    q([],[]).
    """)


def test_geom_unfold():
    p1 = Program("""
    x += b.
    x += a * b.
    x += a * a * x.

    inputs: a; b.
    outputs: x.
    """)

    p0 = Program("""
    x += b.
    x += a * x.

    inputs: a; b.
    outputs: x.
    """)

    assert p0 in p1.to_collection().reversible_megafolds()

    p2 = Program("""
    x += b.
    x += a * b.
    x += a * a * b.
    x += a * a * a * x.

    inputs: a; b.
    outputs: x.
    """)

    r = p2.fold_proposals(p2).xs[1]
    print(r)

    assert Program('x += x * a * a.').rules[0].same(r)

    have = Program([r]) + (p2 - {2,3})
    assert have == p1

    print(have)

    # although this is a valid fold, it is not a simple reversible fold because
    # it doesn't satisfy the reversibility condition when using the resulting
    # program as the unfolding definitions
    have.unfold(0,0).compare(p2)

    # The following unfold happens to work, but it's not a valid sequence: We
    # are trying to find p0 and this assumes we have it.
    have.unfold(0,0,defs=p0).assert_equal(p2)

    # Why can't we use the undo operation - same problem: it requires p0 to work
    # in this instance.

#    for x in p2.to_collection().unfolds().reversible_megafolds().all_partial_megafolds().dedup():
#        print(x)

    # Now, if we take the following program - which is reachable without
    # auxiliary definitions - we can refold it
    p3 = Program("""
    x += b.
    x += a * b.
    x += a * a * b.
    x += a * a * a * b.
    x += a * a * a * a * x.

    inputs: a; b.
    outputs: x.
    """)

    assert p1 in p3.to_collection().reversible_megafolds()
    assert p0 in p3.to_collection().reversible_megafolds().reversible_megafolds()


if __name__ == '__main__':
    from arsenal import TestingFramework
    tf = TestingFramework(globals())
    tf.cli.add_argument('--debug', type=int, default=0)
    verbosity = tf.cli.parse_args().debug
    tf.run()
