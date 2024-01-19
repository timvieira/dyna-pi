from arsenal import colors, assert_throws
from arsenal.maths.combinatorics import choose
from dyna import Program, CostDegrees, term, unifies, Rule, \
    ProgramCollection, DynaParserException, gen_functor


#def test_race():
#    from dyna.benchmarks.collection import benchmark as collection
#    from dyna.cost import CostFunctionWallclock
#
#    b = collection['cky3']
#    D = b.input_data
#    p = b.src
#
#    ss = p.to_collection().slashes()
#    print(len(ss))
#
#    f = CostFunctionWallclock(data=D, solver=2)
#
#    r = ss.race(run=f, tmin=0.001)


def chain_of_cycles(T, a=0.9):
    return Program(
        f'output: x{T}.'
        + 'x0 += 1.'
        + "\n".join(f'x{t} += x{t-1}. x{t} += {a} * x{t}.' for t in range(1, 1+T))
    )


def test_scc_solver():
    p = chain_of_cycles(10)

    p.scc_solver().assert_equal(p.solve())

    p = Program("""
    f += 1.
    f += 0.5 * g.
    g += 1 * f.

    h += g.           % this SCC is not useful
    h += 0.5 * h.

    output: g.

    """)

    p.scc_solver(solver=1).assert_equal("""
    f += 2.
    g += 2.
    % h += 8.   <=== not computed because its not useful
    """)

    p = Program("""
    f(X) += 1.
    f(X) += 0.5 * f(X).

    g(X) += f(X).
    g(X) += 0.5 * g(X).

    h(X) += g(X).           % this SCC is not useful
    h(X) += 0.5 * h(X).

    output: g(X).

    """)

    p.scc_solver(solver=2).assert_equal("""
    f(X) += 2.
    g(X) += 4.
    % h(X) += 8.   <=== not computed because its not useful
    """)


def test_program_collection1():

    # can't unfold an input
    assert len(Program("""
    f(X) += g(X).
    inputs: g(_).
    """).unfolds()) == 0

    # can unfold a non-builtin
    assert len(Program("""
    f(X) += g(X).
    """).unfolds()) == 1

    # can unfold a non-builtin
    assert len(Program("""
    f(X) += g(X).
    tmp += 1.
    """).unfolds(heads=term('f(X)'))) == 1

    assert len(Program("""
    f(X) += g(X).
    """).unfolds(body=term('f(X)'))) == 0

    assert len(Program("""
    f(X) += g(X).
    """).unfolds(body=term('g(X)'))) == 1

    p = Program("""
    x += a * y.
    x += b * y.

    r += a.
    r += b.

    inputs: a; b; y.
    outputs: x.
    """)

    q = Program("""

    x += r * y.

    r += a.
    r += b.

    inputs: a; b; y.
    outputs: x.

    """)

    assert p.partial_megafolds(p).partial_megafolds(p) == ProgramCollection([q])
    assert p.megafolds() == ProgramCollection([q])
    assert p.megafolds().megafolds(p) == ProgramCollection([q])   # no more folds
    assert p.reversible_megafolds() == ProgramCollection([q])
    assert p.reversible_megafolds().reversible_megafolds() == ProgramCollection([q])

    assert q.unfolds() == ProgramCollection([p])
    assert q.unfolds().unfolds() == ProgramCollection([p])  # no more unfolds

    assert ProgramCollection([p, q]).prune().sort(Program.__len__) \
        == [p.prune(), q.prune()]

    assert ProgramCollection([p, p.prune(), q]).prune().dedup().sort(Program.__len__) \
        == [p.prune(), q]

    assert ProgramCollection([p, p.prune(), q])[0] == p
    assert ProgramCollection([p, p.prune(), q])[[0,2]] == [p, q]

    c = ProgramCollection([p, q]).prune()
    c.min_degree().assert_equal(p.prune())
    c.max(Program.degrees).assert_equal(q.prune())
    assert c.sort_degree() == [p.prune(), q.prune()]
    assert c.groupby(len) == {2: [p.prune()], 3: [q.prune()]}

    print(Program("goal += f(X) * g(Y).").to_collection().eurekas())


def test_collection2():

    p = Program("""

    path([X1,X2|Xs]) += edge(X1,X2) * path([X2|Xs]).
    path([X]) += stop(X).
    goal += start(X) * path([X|Xs]).

    inputs: start(_); edge(_,_); stop(_).
    outputs: goal.
    """)

    import dyna
    m = dyna.make_smt_measure(p)

    C = (p.to_collection()
         .eurekas()
         .unfolds_first()
         .dedup()
         .folds_seq()
         .filter(m.safe)
         .prune_fast()
         .dedup()
    )

    print(f'{len(C)} nodes')
    assert len(C) == 15
    print(C.min(dyna.Program.degrees))

    C.graph._repr_html_()


def test_buckets():
    from dyna import canonicalize

    p = Program("""
    f(X).
    f(X) += 2.
    f(X) += 3.

    a += 2.
    a += 1.
    """)

    assert len(p) == 5
    assert p._buckets is None   # no reason to have buckets because update was never called.

    for r in Program("a += 3.  f(X) += 0."): p.append(r)
    assert p._buckets is not None

    print(p._buckets)
    assert p._buckets == {canonicalize(term('f(X)')): 0, canonicalize(term('a')): 3}

    assert len(p) == 5   # number of rules unchanged because new rules were folded into to existing rule

    # runs constant folding
    p.assert_equal("f(X) += 6. a += 6.")


def test_normalize():

    p = Program("""

    f(X,g(h(Y))) += (X=Y) * 2.

    """)

    q = p.normalize_unification2()
    print(q)

    q.assert_equal("""

    f(X,G) += (G=g(H)) * (H=h(Y)) * (X=Y) * 2.

    """)

    q.snap_unifications().assert_equal(p.snap_unifications())

    p = Program("""
    goal += 1 is 2+4.
    f(X,Y) += X is 2+4, Y is X+1.
    g(X,Y) += Y is X+1, X is 2+4.   % check that constraint order does not matter

    """).run_builtins().assert_equal("""
    % goal is dead
    f(6,7).
    g(6,7).
    """)


def test_trivial_rename():
    p = Program('a += 1.')
    q = Program('b += 1.')
    print(p)
    print(q)
    assert p.trivial_rename(q) is not None
    assert q.trivial_rename(p) is not None

    print(colors.line(80))
    p = Program('f(X,Y) += h(X,Y).')
    q = Program('g(Y,X) += h(X,Y).')
    print(p)
    print(q)
    assert p.trivial_rename(q) is not None
    assert q.trivial_rename(p) is not None

    print(colors.line(80))
    p = Program('f(X,X) += h(X,X).')
    q = Program('g(Y,X) += h(X,Y).')
    print(p)
    print(q)
    r = p.trivial_rename(q)
    print(r)
    print(q.trivial_rename(p))
    assert p.trivial_rename(q) is not None and q.trivial_rename(p) is None

    print(colors.line(80))
    p = Program('f1(X,Y) += g(X,Y) * h(Y,Z).')
    q = Program("f2([Y',X',q(X')]) += h(Y',Z') * g(X',Y').")
    print(p)
    print(q)
    print(p.trivial_rename(q))
    print(q.trivial_rename(p))
    assert p.trivial_rename(q) is not None
    assert q.trivial_rename(p) is not None

    print(colors.line(80))
    p = Program('a += 1. a += 2.')
    q = Program('b += 2. b += 1.')
    print(p)
    print(q)
    print(p.trivial_rename(q))
    print(q.trivial_rename(p))
    assert p.trivial_rename(q) is not None
    assert q.trivial_rename(p) is not None

    # This example does not work because it requires deeper rewriting (i.e., it
    # is not "trivial")
    print(colors.line(80))
    p = Program('a += 1. a += 0.5 * a.')
    q = Program('b += 1. b += 0.5 * b.')
    print(p)
    print(q)
    assert p.trivial_rename(q) is None
    assert q.trivial_rename(p) is None

    print(colors.line(80))
    p = Program("matched(N',S') += sumlist(Xs,N') * sort(Xs,S').")
    q = Program("matched(N',S') += sumlist(Xs,N') * sort(Xs,S').")
    print(p)
    print(q)
    pq = p.trivial_rename(q)
    qp = p.trivial_rename(q)
    print(pq)
    print(qp)
    assert pq is not None
    assert qp is not None

    print(colors.line(80))
    p = Program("goal += a * b * c.")
    q = Program("goal' += a * b.")
    print(p)
    print(q)
    assert len(p.partial_megafolds(q)) == 1
    pq = p.trivial_rename(q)
    qp = p.trivial_rename(q)
    print(pq)
    print(qp)
    assert pq is None
    assert qp is None


def test_instantiate():
    path = Program("""
    goal += beta([X|Xs]) * start(X).
    beta([X,Y|Xs]) += beta([Y|Xs]) * edge(X,Y).
    beta([X]) += stop(X).

    inputs: start(_); edge(_,_); stop(_).
    outputs: goal.
    """)

    D = """
    start(a) += 1.
    edge(a,a) += 0.5.
    stop(a) += 1.
    """

    chart = (path+D).seminaive(5)
    path.instantiate(chart).assert_equal("""
    goal += beta([a, a, a, a]) * start(a).
    goal += beta([a, a, a]) * start(a).
    goal += beta([a, a]) * start(a).
    goal += beta([a]) * start(a).
    beta([a, a, a, a, a]) += beta([a, a, a, a]) * edge(a,a).
    beta([a, a, a, a]) += beta([a, a, a]) * edge(a,a).
    beta([a, a, a]) += beta([a, a]) * edge(a,a).
    beta([a, a]) += beta([a]) * edge(a,a).
    beta([a]) += stop(a).
    """)

    lcpath = path.lct({0:0, 1:0, 2:0}).prune(max_depth=4)
    lcpath.instantiate((lcpath + D).seminaive()).assert_equal("""
    goal / beta([a|Xs]) += goal / beta([a,a|Xs]) * edge(a,a).
    goal / beta([a|Xs]) += goal / goal * start(a).
    goal / stop(a) += goal / beta([a]).
    goal += goal / stop(a) * stop(a).
    goal/goal.
    """)


def test_program_comparisons():
    a = Program("""
    g(X,Y) :- f(X).
    g(X,Y) :- h(X).
    f(X).
    f(X,X).
    """)
    b = Program("""
    f(Y).
    f(X,Y).
    g(X,Y) :- notf().
    g(Y,X) :- h(Y).
    """)

    a.compare(b)
    assert a.align(b) == [(0, None), (1, 3), (2, 0), (3, None), (None, 1), (None, 2)]
    assert a != b

    #print()
    #a.showdiff(b)

    a = Program("""
    f(X).
    f(X,X).
    g(X') += h(X', Y) * f(X').
    """)
    b = Program("""
    f(Y).
    g(X) += f(X) * h(X, Y).
    f(Y,Y).
    """)
    a.assert_equal(b)
    assert not (a != b)
    assert a == b

    print()
    print(colors.yellow % 'Cases involving empty programs')
    # weird cases involving empty programs
    z = Program('')
    a.compare(z)
    print()
    z.compare(b)
    print()
    z.compare(z)
    z.assert_equal(z)


def test_parse_annotations():

    p = Program("""

    goal += f(N).

    inputs: f(X) ; g(X, Y).
    params: h(Z).
    outputs: goal.

    """)

    assert len(p.inputs) == 3
    assert len(p.outputs) == 1


def test_degrees():

    p = Program("""
    goal += f(I) * h(I,J).
    h(I,K) += f(I,J) * g(J,K).
    """)

    q = Program("""
    goal += f(I) * f(I,J) * g(J,K).
    """)

    r = Program("""
    goal += tmp(J) * g(J,K).
    tmp(J) += f(I) * f(I,J).
    """)

    assert p.degrees() == CostDegrees((3,2))
    assert q.degrees() == CostDegrees((3,))
    assert r.degrees() == CostDegrees((2,2))

    print(sorted([p.degrees(), q.degrees(), r.degrees()]))


# TODO: test under different semirings!
def test_constant_folding():

    p = Program("""

    f(X,Y).
    f(X,Y) += 0.
    f(X,Y) += 1.
    f(3,Y) += 1.
    f(X,4) += 1.
    f(3,4) += 1*7.

    goal += 1*2.
    goal += 1.

    goal += f(3,4).

    goal += f(X,Y) * f(Y,Z).


    """, '', '')

    p.constant_folding().assert_equal("""
    goal += f(3, 4).
    goal += f(X, Y) * f(Y, Z).
    f(X, Y) += 2.
    f(3, Y) += 1.
    f(X, 4) += 1.
    f(3, 4) += 7.
    goal += 3.
    """)


#def test_search():
#    import dyna.benchmarks.collection as B
#    p = B.benchmark['chain-05'].src
#
#    def checkpoint(x):
#        checkpoint.n += 1
#    checkpoint.n = 0
#
#    opt = p.beam(20,1,checkpoint)
#    p(opt.best, 1)
#    assert opt.best.degree == 2
#    assert checkpoint.n > 0
#
#    assert len(list(opt.top(5))) == 5
#    opt.show_top()
#
#    opt = p.mcts(30)
#    p(opt.best, 1)
#    assert opt.best.degree == 2


def test_cost1():
    """
    Test optimizers with custom cost function
    """

    p = Program("""
    goal += a * b.
    b += c * x * y.
    b += c * x * c * x.
    b += c * x * c * x.
    b += c * x * c * x.

    inputs: x; a; c; y.
    outputs: goal.
    """)

    p2 = Program("""
    goal += a * b.
    b += cx * y.
    b += cxcx.
    b += cxcx.
    b += cxcx.

    cx += c * x.
    cxcx += cx * cx.

    inputs: x; a; c; y.
    outputs: goal.
    """)

    D = Program("""
    x += 1.
    a += 2.
    c += 3.
    y += 4.
    """)

    print((p+D).sol())
    print((p2+D).sol())

    #print(Program.cost_prefix_firings(D='',budget=1))
    #cost = Program.cost_prefix_firings(D)
    def cost(q):
        q = q.prune()
        s = q.solver()
        s(D)
        have = s.user_query('goal')
        want = 'goal += 78.'
        if have != want and len(s.agenda) == 0:
            print()
            print(colors.light.red % 'test failed when evaluating cost:')
            have.compare(want)
            raise AssertionError()
        return s.prefix_firings

    beam = p.beam(100, 10, cost=cost,
                  TRANSFORMS=[
                      'fold+',
                      #'unfold',
                      #'megafold-defs',
                      'megafold',
                  ],
                  graph=1,
                  tidy=0,
    )

    beam.best.show_transforms()
    beam.best.show_transforms(show_program=True)

    beam.show_top(5)

    # Run the others just to improve test coverage...
    #mcts = p.mcts(50, cost=cost,
    #              TRANSFORMS=['fold+', 'unfold', 'megafold'],
    #              graph=1, tidy=0)

    print('orig:', cost(p))
    print('manual:', cost(p2))
    print(cost(beam.best), beam.best.prune())
    #print(mcts)

    beam = p.beam(100, 10, cost=cost,
                  TRANSFORMS=[
                      'fold+',
                      'unfold',
                  ],
                  graph=2,
                  tidy=0,
    )



def test_fancy_steps():

    # TODO: Neither of these programs converges because the RHS is not a simple
    # constant - this means that vertical_constant_folding does not merge their
    # values.  Perhaps it should.  Another thought is that this type of folding
    # could/should be left for something like speculation (kind of weird to
    # imagine speculation running in the "projection" step of forward chaining,
    # but maybe not?)  Related to: https://github.com/timvieira/dyna-pi/issues/23
    from dyna.propagate import ConstraintPropagation
    rewrites = ConstraintPropagation('')   # propagation only removes duplicates in this case.

    def proj(p):
        q = []
        for r in p:
            u = rewrites(r.body)
            if u is None: continue
            q.append(Rule(r.head, *u))
        return Program(q, p.inputs, p.outputs, p.semiring).constant_folding()

    p = Program("""
    a(X,Y) += 1 * (X < Y).
    a(X,Y) += a(X,Y) * 0.5 * (X < Y).
    """)

    m = p.fc(max_iter=6, proj=proj)
    print(m)

    #m2 = p.solver3()(max_iter=7).sol()
    #m.assert_equal(m2)


def test_step():
    #from dyna.benchmarks.cky import CKY
    #cky = CKY()
    #p = cky.src.step(cky.src)
    #assert not cky(p, 5)['timeout']

    p = Program("""
    x += a * x.
    x += b.

    inputs: a; b.
    """)
    p.step(p).step(p).step(p).step(p).assert_equal("""
    x += a * a * a * a * a * x.
    x += a * a * a * a * b.
    x += a * a * a * b.
    x += a * a * b.
    x += a * b.
    x += b.
    """)

    p = Program("""
    x += a * x * x.
    x += b.

    inputs: a; b.
    """)
    p.step(p).assert_equal("""
    x += a * (a * x * x) * (a * x * x).
    x += a * (a * x * x) * (        b).
    x += a * (        b) * (a * x * x).
    x += a * (        b) * (        b).
    x += b.
    """)

    p = Program("""
    a(X) += 1.
    a(X) += a(X) * 0.5.
    """)
    p.fc(max_iter=20).assert_equal("a(X) += 2.0.")
    p.fc(max_iter=3).assert_equal("a(X) += 1.75.")
    p.fc(None).assert_equal("a(X) += 2.")


# XXX: Experimental feature
def test_semiring_builtins():
    from semirings import minmax

    p = Program("""

    goal += $lift(5).
    goal += $lift(2).

    """, semiring=minmax(1000, -1))

    print(p.fc())


    p = Program("""

    goal += $lift("a").
    goal += $lift("b").

    """, semiring=minmax("z", ""))

    print(p.fc())


def test_foo():

    x = Program("""
    a += b * c.
    """)

    print(x)

    a,b,c = map(term,'abc')
    assert list(x) == [Rule(a, b, c)]


def test_builtin_ops():

    Program('goal += X < 2.').sol().assert_equal('goal += X < 2.')
    Program('goal += 1 < 2.').sol().assert_equal('goal.')
    Program('goal += 1 != 2.').sol().assert_equal('goal.')
    Program('goal += 1 != 1.').sol().assert_equal('')

    Program('goal += $not_matches("f(X)", f(3)).').sol().assert_equal('')
    Program('goal += $not_matches("f(X)", g(3)).').sol().assert_equal('goal.')
    Program('goal += $not_matches("f(h(X))", f(Y)).').fc().assert_equal('goal += $not_matches("f(h(X))", f(Y)).')
    Program('goal += $not_matches("f(X)", f(Y)).').fc().assert_equal('')
    Program('goal(Z) += Y=f(Z), $not_matches("f(X)", Y).').fc().assert_equal('')
    Program('goal(Z) += $not_matches("f(X)", Y), Y=f(Z).').fc().run_builtins().assert_equal('')

    Program('goal += 0 <= X <= Y < 3.').assert_equal('goal += (0 <= X) * (X <= Y) * (Y < 3).')

    with assert_throws(DynaParserException):
        Program('goal += 0 <= X <= Y < 3')  # missing period


def test_unfold_x():

    p = Program("""

    goal += x.
    goal += x.

    x += 1.

    outputs: goal.

    """)

    p.unfold_x(term('x'), verbosity=1000).assert_equal('goal += 1. goal += 1.')


def test_slashes():

    path = Program("""
    goal += beta([X|Xs]) * start(X).
    beta([X,Y|Xs]) += beta([Y|Xs]) * edge(X,Y).
    beta([X]) += stop(X).

    inputs: start(_); edge(_,_); stop(_).
    outputs: goal.
    """)

    D = """
    start(a) += 1.
    edge(a,a) += 0.5.
    stop(a) += 1.
    """

    C = path.to_collection().lct().prune(max_depth=4)
    assert len(C) == 18

    # It's possible that the racing method might give inconsistent winners as it uses wallclock time.
    (best_t, best_x, best_y) = C.prune_fast().race(run = lambda p: p(D, solver=2), tmin=0.01)
    print(best_y)

    best_x.assert_equal("""
    (goal / goal).
    (goal / beta([X|Xs])) += start(X) * goal / goal.
    (goal / beta([Y|Xs])) += edge(X,Y) * goal / beta([X,Y|Xs]).
    (goal / stop(X)) += goal / beta([X]).
    goal += stop($X0) * goal / stop($X0).
    """)


def test_program_collection_stuff():

    path = Program("""
    goal += start(X) * beta([X|Xs]).
    beta([X,Y|Xs]) += edge(X,Y) * beta([Y|Xs]).
    beta([X]) += stop(X).

    inputs: start(_); edge(_,_); stop(_).
    outputs: goal.
    """)

    D = """
    start(a) += 1.
    edge(a,a) += 0.5.
    stop(a) += 1.
    """

    gen_functor.reset()
    C = path.to_collection().eurekas().folds_seq().unfolds_seq().folds_seq().prune(max_depth=4).dedup()
    assert len(C) == 15, len(15)

    # It's possible that the racing method might give inconsistent winners as it uses wallclock time.
    (best_t, best_x, best_y) = C.prune_fast().race(run = lambda p: p(D, solver=2), tmin=0.01)
    print(best_y)

    best_x.assert_equal("""
    goal += start(X) * $gen1(X).
    $gen1(X) += edge(X,Y) * $gen1(Y).
    $gen1(X) += stop(X).
    """)


if __name__ == '__main__':
    from arsenal.testing_framework import testing_framework
    testing_framework(globals())
