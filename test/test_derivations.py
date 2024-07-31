from arsenal import iterview
from arsenal.iterextras import take
from collections import Counter

from dyna import Symbol, Program, Term, Derivation, term
from dyna.transform.measure import make_smt_measure


def run_sequence_tests(ps, x, T):
    "Transform derivations between all pairs of programs in the sequence `ps`."
    Ds = [p.derivations(T, x) for p in iterview(ps, 'derivations', transient=1)]

    # TODO: ressurect these tests
    if 0:

        for p, D in zip(ps, Ds):
            measure = make_smt_measure(p.root)
            m_p = measure(p)
            m_r = measure(p.root)

            for d_p, d_r in zip(D, D.transform(p.root)):
                #print('size:', dt.size(), '==>', d.size(), dt.measure(), d.measure())

                msg = f"""\
root rule measure: {m_r}
target rule measure: {m_p}
root derivation:   {d_r}
target derivation: {d_p}
root measure: {m_r.derivation_measure(d_r)}
target measure estimate: {m_p.derivation_measure(d_p)}
"""
                import z3

                x = m_p.derivation_measure(d_p)
                y = m_r.derivation_measure(d_r)

                # Probably not quite right to test in this way because what we
                # are actually after is at test that is for all values of the
                # clause measures.
                solver = z3.Solver()
                solver.add(y.lo <= x.lo, x.hi <= y.hi)
                assert solver.check() == z3.sat
                #print(solver.model())

                #assert y.lo <= x.lo and x.hi <= y.hi

                #assert m_p.derivation_measure(d_p) in m_r.derivation_measure(d_r), msg

    for D in iterview(Ds, 'mapping', transient=1):
        for p, Dp in zip(ps, Ds):
            for d in D:
                dp = d.p.Transform(d, p)
                assert dp in Dp or dp.height() > T


def test_sp():

    p = Program("""
    p += b.
    p += p * a.
    sp += s * p.

    outputs: sp.
    """, semiring=Symbol)

    p.update(Term('a'), Symbol('a'))
    p.update(Term('b'), Symbol('b'))
    p.update(Term('s'), Symbol('s'))

    p = p.elim_p(3).elim_p(3).elim_p(3)
    p = Program(p, semiring=p.semiring, inputs=p.inputs, outputs=p.outputs)

    p1 = p.unfold(2,1)
    p2 = p1.megafolds(p)[1]

    p3 = p.unfold(1,1)   # requires going up to the root of the transform tree and the over

    run_sequence_tests([p,p1,p2,p3], 'sp', T=5)



def test_startpath():
    p0 = Program("""
    path(I,K) += edge(I,K).
    path(I,K) += path(I,J) * edge(J,K).
    startpath(K) += start(I) * path(I,K).

    outputs: startpath(K).
    """, semiring=Symbol)

    p0.update(term('edge(1,2)'), Symbol('a'))
    p0.update(term('edge(2,3)'), Symbol('b'))
    p0.update(term('edge(3,4)'), Symbol('c'))
    p0.update(term('edge(4,5)'), Symbol('d'))
    p0.update(term('start(1)'), Symbol('x'))

    p1 = p0.unfold(2, 1)
    p2 = p1.megafolds(p0)[1]

    run_sequence_tests([p0, p1, p2], 'x', T=15)


def test_catalan():

    p0 = Program("""
    x += b.
    x += x * x.

    outputs: x.
    """, semiring=Symbol)

    p0.update(Term('a'), Symbol('a'))
    p0.update(Term('b'), Symbol('b'))
    p0 = p0.elim_p(2).elim_p(2)
    p0 = Program(p0, semiring=p0.semiring, inputs=p0.inputs, outputs=p0.outputs)

    p1 = p0.unfold(1, 1, defs=p0)

    run_sequence_tests([p0,p1], 'x', T=3)

    p2 = p1.basic_fold(p0.rules[p1.i], p1.j, p1.new2def)
    p2.defs = p2
    assert p2 == p0

    run_sequence_tests([p0,p2], 'x', T=3)

    # TODO: not working yet
#    run_sequence_tests([p,p1,p2], 'x', T=3)


def test_geom():
    p0 = Program("""
    x += `b`.
    x += `a` * x.

    outputs: x.
    """, semiring=Symbol)

    p1 = p0.unfold(1, 1)

    p2 = p1.unfold(2, 2, defs=p0)

    p2.undo.assert_equal(p1)
    p1.undo.assert_equal(p0)
    assert p2.undo == p1
    assert p1.undo == p0

    run_sequence_tests([p0, p1, p2], 'x', T=4)


def test_explicit_path():

    p0 = Program("""
    b(X) += beta([X|Xs]).

    beta([X,Y|Xs]) += beta([Y|Xs]) * edge(X,Y).
    beta([X]) += stop(X).

    % tiny data set
    start(a) += 1.
    edge(a,a) += 0.5.
    stop(a) += 1.

    outputs: b(X).
    """)

    p1 = p0.unfold(0,0)
    p2 = p1.megafolds(p0)[0]

    P0 = p0.derivations(5, 'b(a)').sort(Derivation.height)
    P2 = p2.derivations(5, 'b(a)').sort(Derivation.height)

    assert all((p0.Transform(d, p2) in P2) for d in P0)
    assert all((p0.Transform(d, p0) in P0) for d in P0)


def test_bad_fold():

    P0 = Program("""
    q += 1.
    p += q.
    """)

    Rs = Program('q += q.')
    Rs.rules[0].j = 0
    bad = P0.partial_megafolds(P0, Rs=Rs)[0]

    print(bad)

    assert len(bad.derivations(5, 'X')) < len(P0.derivations(5, 'X'))

    # When we try to map the proof from the larger set over to the smaller set,
    # we will hit a recursion error.
    for d in P0.derivations(5, 'X'):
        print()
        print(d)
        try:
            print(P0.Transform(d, bad))
        except AssertionError as e:
            print('<expected error>')
            print('hit expected assertion error')
            print(e)
            print('</expected error>')
        except RecursionError:
            print('hit expected recursion error')
        else:
            assert 0


# TODO: add some actual assertions to this test...
def test_builtins():
    p = Program("""
    goal += y(5).
    y(N) += y(N') * (N' is N - 1) * g(N).
    y(0) += z * g(0).
    y(0) += w * g(0).
    z += `a`.
    w += `b`.
    g(N) += `c`.

    outputs: w.
    """, semiring=Symbol)

    print(p)
    print()

    p.derivations(10,'goal').render_terminal()


def test_seminaive():

    # finite set
    p = Program("""
    x += `b`.
    x += `a`.

    y += x * x.

    z += y.

    outputs: y.
    """, semiring=Symbol)

    D = p.derivations_seminaive(None, 'y', verbose=0)
    assert len(D) == 4
    a, b = Symbol('a'), Symbol('b')
    assert Counter([d.value() for d in D]) == Counter([(b, b), (a, b), (b, a), (a, a)])

    p = Program("""
    x += `b`.
    x += `a` * x * x.

    outputs: x.
    """, semiring=Symbol)

    D = p.derivations_seminaive(4, 'x', verbose=0)

    assert len(set(D)) == len(D)
    assert set(D) == set(p.derivations(4, 'x'))


def test_agenda():

    p = Program("""
    f(1) += 2.
    g(1) += 3.
    g(2) += 4.
    goal += g(X) * f(X).
    """)

    have = set(p.derivations_agenda())
    want = set(p.derivations(None, 'X'))
    assert have == want

    p = Program("""
    x += `b`.
    x += `a` * x.

    outputs: x.
    """, semiring=Symbol)

    want = set(p.derivations(4, 'X'))
    have = set()
    for d in p.derivations_agenda():   # pragma: no branch
        if d.height() > 4: break
        have.add(d)
    assert have == want


def todo_visualizations():

    p = Program("""
    x += `b`.
    x += `a` * x.

    outputs: x.
    """, semiring=Symbol)

    Ds = p.derivations(3, 'x')

    Ds[[1,2]].render_tikz()
    Ds.render_graphviz()
    Ds[0].render_tikz()
    Ds.to_forest()
    Ds._repr_html_()
    Ds[0]._repr_html_()


def test_misc():

    p = Program("""
    x.
    x += 0.5 * x.

    outputs: x.
    """)

    Ds = p.derivations(3, 'x')

    assert len(Ds + Ds) == len(Ds) * 2

    assert len(Ds + Ds[0]) == len(Ds) + 1
    assert len(Ds[0] + Ds[1] + Ds[[0,1,2]]) == 5

    assert list(map(Derivation.size, Ds)) == [1,2,3]
    assert list(map(Derivation.height, Ds)) == [1,2,3]
    assert list(map(Derivation.dimension, Ds)) == [0,1,1]

    for x in Ds:
        for y in Ds:
            print(Derivation.is_subtree(x, y))

    assert [Derivation.value(x) for x in Ds] == [(), (0.5,), (0.5, 0.5)]

    p = Program("""
    x += 1.
    y += x.
    x += y * y.

    outputs: x.
    """)

    Ds = p.derivations(7, 'x')

    assert (
        list(map(Derivation.height, Ds))
        == [
            1, 3, 5, 7, 7, 7, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7
        ]
    )

    assert (
        Counter(map(Derivation.dimension, Ds))
        == Counter([
            0, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2,
            2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3
        ])
    )

    assert (
        Counter(map(Derivation.size, Ds))
        == Counter([
            1, 5, 9, 13, 13, 17, 9, 13, 17, 17, 21, 13, 17, 21, 21,
            25, 13, 17, 21, 21, 25, 17, 21, 25, 25, 29
        ])
    )


def test_left_recursion():
    p = Program("""
    x += x * 0.5.   % this *rule* ordering is bad for SLD, but permuting is fine
    x += 1.
    """)

    T = 5

    print('SLD strategy (left recursion)')
    from arsenal import assert_throws
    with assert_throws(RecursionError):
        for t, d in take(T, enumerate(p.sld('x'), start=1)):  # pragma: no branch
            assert False, 'should not happen'

    q = Program("""
    x += 1.
    x += x * 0.5.   % this *rule* ordering is ok for SLD
    """)

    print('SLD strategy (right recursion)')
    for t, d in take(T, enumerate(q.sld('x'), start=1)):
        print(t, d)


def test_geom():

    q = term('x(T")')
    p = Program("""
    x(T) += 1.
    x(T) += a * x(T).
    a += 0.5.
    """)

    for i, proof in take(10, enumerate(p.sld(q))):
        print()
        print(f'proof #{i}: {q}')
        print('proof:', proof)


def test_builtin():

    p = Program("""
    f(0).
    f(Y) += f(X), X < 5, Y is X+1, Y < 5.
    """)

    want = """
    f(0) += 1.0.
    f(1) += 1.0.
    f(2) += 1.0.
    f(3) += 1.0.
    f(4) += 1.0.
    """

    for i, d in take(4, enumerate(p.sld('f(X)'))):
        print(f'\nproof #{i}')
        print(d)


def test_builtins2():

    p = Program("""
    asum([], 0).
    asum([X|Xs], S) :-
      asum(Xs,S'), A is abs(X), S is A + S'.

    listmax([], -10000).
    listmax([X|Xs], M) :-
      listmax(Xs, M'), M is max(X, M').

    """)

    r = Program()
    for d in p.sld('listmax([1,2,1,3,2], M)'):
        r.append(d)
    assert r.rules[0].head.args[1] == 3

    r = Program()
    for d in p.sld('asum([1,-2,1,-3,2], S)'):
        r.append(d)
    assert r.rules[0].head.args[1] == 9


def test_builtins1():

    p = Program("""
    f(0).
    f(Y) += Y is X+1, Y < 5, Y >= 0, f(X).
    """)

    want = """
    f(0) += 1.0.
    f(1) += 1.0.
    f(2) += 1.0.
    f(3) += 1.0.
    f(4) += 1.0.
    """

    assert len(list(p.sld('f(4)'))) == 1
    assert len(list(p.sld('f(8)'))) == 0
    #print(SLD(Program('goal += X>5.')).user_query('goal'))


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
