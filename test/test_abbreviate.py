import pytest
from arsenal import colors

from dyna import Program


def test_simple_geom1():
    # The self-recursive phantom x(I) lifts to a scalar; the sound normalizer
    # produces `x_p += 1. x_p += 0.5*x_p. x(_) += x_p.` -- the same reduction
    # abbreviate's `$free` did, now sound (PhantomProjection, greatest fixpoint).
    p = Program("""
    % lifted geometric series
    x(I) += 1.
    x(I) += 0.5 * x(I).

    outputs: x(_).
    """)

    ps = p.sol()
    ps.assert_equal("""
    x(I) += 2.
    """)

    q = p.normalize_range_restriction()

    print(colors.orange % 'normalized program:', q)

    q.assert_equal("""
    x(I) += x_1_p.
    x_1_p += 1.
    x_1_p += 0.5 * x_1_p.
    """)

    qs = q.sol()

    check(qs, ps)


def test_infinite_multiplicity():
    # The f(1)/f(X) constant overlap value-splits (f = f_dft + f_spc, sound by
    # linearity of +); summing the open f_dft over the universe gives goal = inf.
    # The sound normalizer reproduces abbreviate's old `$free` values.
    p = Program("""

    goal += f(X).

    f(1) += 2.
    f(X) += 3.

    g(X) += 4 * f(X).

    outputs: goal.

    """)

    ps = p.sol()

    ps.assert_equal("""
    f(X) += 3.0.
    f(1) += 2.0.
    goal += ∞.

    g(X) += 12.
    g(1) += 8.

    """)

    q = p.normalize_range_restriction()

    q.assert_equal("""
    f(X) += f_1_dft.
    f(X) += f_1_spc(X).
    f_1_dft += 3.
    f_1_spc(1) += 2.
    g(X) += 4 * f_1_dft.
    g(X) += 4 * f_1_spc(X).
    goal += f_1_dft * ∞.
    goal += f_1_spc(X).
    """)

    qs = q.sol()
    #print(qs)

    qs.assert_equal_query('goal', float('inf'))

    #ps.compare(qs)
    check(qs, ps)


def test_abbreviate_basics2():

    p = Program("""

    goal(X) += f(X,Y) * g(Y).

    f(X,Y) += 2 * g(Y).
    f(1,Y) += 3 * g(Y).

    inputs: g(Y).
    outputs: goal(X).

    """)

    D = """
    g(1).
    g(2).
    g(3).
    """

    ps = (p + D).sol()

    q = p.abbreviate()
    print('abbreviated:', q)
    qs = (q + D).sol()

    for q in ['goal(X)']:
        print(colors.light.yellow % '\nquery:', q)
        want = ps.user_query(q)
        qs.assert_equal_query(q, want)
        have = qs.user_query(q)
        have.compare(want)


    #ps.compare(qs)
    check(qs, ps)


def test_abbreviate_basics1():

    p = Program("""

    goal(X) += f(X) * h(X).

    foo(X) += f(X) * (X is 1+1).

    f(X) += 3.
    f(1) += 3.

    h(1).
    h(2).
    h(3).

    outputs: goal(X); foo(X).

    """, '')

    ps = p.sol()

    q = p.abbreviate()
    qs = q.sol()

    for q in ['goal(X)', 'foo(X)']:
        print(colors.light.yellow % '\nquery:', q)
        want = ps.user_query(q)
        qs.assert_equal_query(q, want)

    #ps.compare(qs)
    check(qs, ps)


def check(have, want):
    # check that the original items are all there and have the same value
    have.compare(want)
    for i,j in have.align(want):
        if j is not None:
            assert i is not None
            assert have.rules[i].same(want.rules[j])


def test_abbreviate_geom2():
    # The sound normalizer value-splits the a(1,Y)/a(X,Y) constant overlap but
    # (correctly) refuses to project the diagonal a(X,X) -- that drop is the
    # unsound $free/startpath3 move.  Values are preserved either way.
    p = Program("""
    % lifted geometric series
    a(X,X) += 1.
    a(1,Y) += 1.
    a(X,Y) += special(Y).
    a(X,Y) += 0.5*a(X,Y).
    goal(X,Y) += a(X,Y).

    inputs: special(Y).
    outputs: X.
    """)
    D = """
    special(2) += 3.
    """

    ps = (p + D).sol()
    ps.assert_equal("""
    a(1, Y) += 2.
    a(X, X) += 2.
    a(X, 2) += 6.
    goal(1, Y) += 2.
    goal(X, 2) += 6.
    goal(Y, Y) += 2.
    special(2) += 3.
    """)

    q = p.normalize_range_restriction()
    print(q)

    # no-op: the diagonal a(X,X) blocks the value-split (it is not a single
    # position), so the program is left untouched -- and crucially the diagonal
    # is NOT projected (that would be the unsound startpath3 move).
    q.assert_equal("""
    a(X,X) += 1.
    a(1,Y) += 1.
    a(X,Y) += special(Y).
    a(X,Y) += 0.5 * a(X,Y).
    goal(X,Y) += a(X,Y).
    """)

    qs = (q + D).sol()

    #ps.compare(qs)
    check(qs, ps)


PAPA_DATA = Program("""
rewrite("ROOT","S","<.>") += 1.0.
rewrite("S","NP","VP") += 1.0.
rewrite("NP","Det","N") += 1.0.
rewrite("NP","NP","PP") += 1.0.
rewrite("VP","V","NP") += 1.0.
rewrite("VP","V") += 1.0.
rewrite("VP","VP","PP") += 1.0.
rewrite("PP","P","NP") += 1.0.
rewrite("<.>",".") += 1.0.
rewrite("NP","Papa") += 1.0.
rewrite("N","caviar") += 1.0.
rewrite("N","spoon") += 1.0.
rewrite("N","fork") += 1.0.
rewrite("N","telescope") += 1.0.
rewrite("N","boy") += 1.0.
rewrite("N","girl") += 1.0.
rewrite("N","baby") += 1.0.
rewrite("N","man") += 1.0.
rewrite("N","woman") += 1.0.
rewrite("N","moon") += 1.0.
rewrite("N","cat") += 1.0.
rewrite("V","ate") += 1.0.
rewrite("V","saw") += 1.0.
rewrite("V","fed") += 1.0.
rewrite("V","said") += 1.0.
rewrite("V","jumped") += 1.0.
rewrite("P","with") += 1.0.
rewrite("P","over") += 1.0.
rewrite("P","under") += 1.0.
rewrite("P","above") += 1.0.
rewrite("P","below") += 1.0.
rewrite("P","on") += 1.0.
rewrite("P","in") += 1.0.
rewrite("Det","the") += 1.0.
rewrite("Det","a") += 1.0.
word("Papa",0,1).
word("ate",1,2).
word("the",2,3).
word("caviar",3,4).
word("with",4,5).
word("a",5,6).
word("spoon",6,7).
word(".",7,8).
length(8).
""")


def test_cky_unary_cycle_factoring():

    p = Program("""
    p(X, I, K) += rewrite(X, Y, Z) * p(Y, I, J) * p(Z, J, K).
    p(X, I, K) += rewrite(X, Y) * p(Y, I, K).
    p(X, I, K) += rewrite(X, Y) * word(Y, I, K).
    goal += length(N) * p("ROOT", 0, N).

    inputs: rewrite(X,Y,Z); rewrite(X,Y); word(W,I,K); length(N).
    outputs: goal.

    """)

    D = PAPA_DATA + Program("""
    rewrite("N", "N1") += .5.
    rewrite("N1", "N2") += .5.
    rewrite("N2", "N3") += .5.
    rewrite("N3", "N4") += .5.
    rewrite("N4", "N5") += .5.
    rewrite("N5", "N") += .5.
    """)
    value = 2.064

    q = p.slash("p(X',I',K')", {1: 1}).prune()

    # Sound degree reduction: the slash span cancels under the `/` quotient
    # (range_restriction.QuotientProjection), replacing the unsound `$free` drop.
    new_program = q.normalize_range_restriction().prune()
    s = (new_program + D).sol()
    s.assert_equal_query('goal', value)
    print(colors.ok)


def test_cky_left_child_slash():

    p = Program("""
    p(X, I, K) += rewrite(X, Y, Z) * p(Y, I, J) * p(Z, J, K).
    p(X, I, K) += rewrite(X, Y) * p(Y, I, K).
    p(X, I, K) += rewrite(X, Y) * word(Y, I, K).
    goal += length(N) * p("ROOT", 0, N).

    inputs: rewrite(X,Y,Z); rewrite(X,Y); word(W,I,K); length(N).
    outputs: goal.

    """)

    D = PAPA_DATA + Program("""
    rewrite("N", "N1") += .5.
    rewrite("N1", "N2") += .5.
    rewrite("N2", "N3") += .5.
    rewrite("N3", "N4") += .5.
    rewrite("N4", "N5") += .5.
    rewrite("N5", "N") += .5.
    """)
    value = 2.064

    q = p.slash("p(X',I',K')", {0: 1}).prune()

    # Run nonground forward chaining
    ps = (p+D).agenda()
    ps.assert_equal_query('goal', value)

    # Run nonground forward chaining
    #qs = q.solver2()(D)
    #qs.assert_equal_query('goal', value)

    # Sound degree reduction: the slash span cancels under the `/` quotient
    # (range_restriction.QuotientProjection), replacing the unsound `$free` drop.
    new_program = q.normalize_range_restriction().prune()
    print(q)
    print(new_program)

    s = (new_program + D).sol()
    s.assert_equal_query('goal', value)
    print(colors.ok)


#def test_sdd():
#    p = Program("""
#    (x(I,J) / tmp(I,J)) += 1.0.
#    (x(I,J) / tmp(I,J)) += 0.5 * x(I,J) / tmp(I,J).
#    $other(tmp(I,J)) += I < J.
#    x(I,J) += $other(tmp(I,J)) * x(I,J) / tmp(I,J).
#    """)
#
#    p = Program("""
#    tmp(I,J) += I < J.
#    x(I,J) += tmp(I,J).
#    """)
#
#    q = p.abbreviate()
#
#    q.assert_equal("""
#    $inst_0(I,J) += I < J.
#    $inst_1(I,J) += $inst_0(I,J).
#    tmp(I,J) += $inst_0(I,J).
#    x(I,J) += $inst_1(I,J).
#    """)


def test_path_list():

    p = Program("""

    beta([X,Y|Xs]) += edge(X,Y) * beta([Y|Xs]).
    beta([X]) += stop(X).
    goal += start(X) * beta([X|Xs]).

    outputs: goal.
    inputs: start(_); edge(_,_); stop(_).
    """)

    D = """
    % tiny data set
    start(a) += 1.
    edge(a,b) += 0.5.
    edge(b,c) += 0.5.
    edge(c,a) += 0.5.
    stop(a) += 1.
    """

    q = p.abbreviate().prune()

    print(colors.orange % 'abbreviated program:', q)

    p_sol = (p + D).sol()
    q_sol = (q + D).sol()

    for output in q.outputs.just_heads():
        print(output, end=' ')
        q_sol.user_query(output).assert_equal(p_sol.user_query(output))
        print(colors.ok)


def test_startpath1():
    # The diagonal path(I,I) is not a `/` quotient, so the sound normalizer
    # leaves it alone (projecting it is the unsound startpath3 move).  Values are
    # preserved; abbreviate's old diagonal-projected shape is deliberately gone.
    p = Program("""

    path(I,I).
    path(I,K) += path(I,J) * edge(J,K).

    goal += start(I) * path(I,K) * stop(K).

    outputs: goal.
    inputs: start(_); edge(_,_); stop(_).
    """)

    D = """
    % tiny data set
    start(a) += 1.
    edge(a,b) += 0.5.
    edge(b,c) += 0.5.
    edge(c,a) += 0.5.
    stop(a) += 1.
    """

    q = p.normalize_range_restriction()

    print(colors.orange % 'normalized program:', q.sort())

    # no-op: path(I,I) is a diagonal, not a `/` quotient -- nothing cancels, so
    # it is left exactly as-is (projecting it is the unsound startpath3 move).
    q.assert_equal("""
    path(I,I).
    path(I,K) += path(I,J) * edge(J,K).
    goal += start(I) * path(I,K) * stop(K).
    """)

    p_sol = (p + D).sol()
    q_sol = (q + D).sol()

    for output in q.outputs.just_heads():
        print(output, end=' ')
        q_sol.user_query(output).assert_equal(p_sol.user_query(output))
        print(colors.ok)


def test_startpath2():
    # Same diagonal (path(I,I)); check the sound normalizer preserves path values
    # on data rather than asserting abbreviate's old diagonal-projected shape.
    path = Program("""

    path(I,I).
    path(I,K) += path(I,J) * edge(J,K).

    inputs: edge(I,J).
    outputs: path(I,K).
    """)

    q = path.normalize_range_restriction()

    # no-op: the diagonal path(I,I) is not a quotient, so it is left as-is.
    q.assert_equal("""
    path(I,I).
    path(I,K) += path(I,J) * edge(J,K).
    """)

    D = "edge(a,b) += 0.5. edge(b,c) += 0.5."
    p_sol = (path + D).sol()
    q_sol = (q + D).sol()
    for query in ['path(a,a)', 'path(a,b)', 'path(a,c)', 'path(b,c)', 'path(c,c)']:
        q_sol.user_query(query).assert_equal(p_sol.user_query(query))


def test_input_dispatch_keeps_user_type_constraints_not_free_bound_markers():

    p = Program("""
    use(I,J) += edge(I,J).

    inputs: edge(I,J).
    outputs: use(I,J).
    """)

    t = p.type_analysis(input_type="""
    edge(I,J) :- n(I), n(J).

    inputs: n(I).
    """)

    q = p.abbreviate(types=t)

    q.assert_equal("""
    edge_0(I,J) += edge(I,J) * n(I) * n(J).
    use(I,J) += use_1(I,J).
    use_1(I,J) += edge_0(I,J).
    """)


def test_default_abbreviation_uses_possible_types_not_useful_types():

    p = Program("""
    goal += a(I,I).
    a(I,K) += b(I,J) * c(J,K).
    goal += dead(X).

    input: b(_,_); c(_,_).
    output: goal.
    """)

    possible = p.abbreviate()
    useful = p.abbreviate(types=p.usefulness_analysis())

    possible.assert_equal("""
    a(I,K) += a_0(I,K).
    b_1(I,J) += b(I,J).
    c_2(J,K) += c(J,K).
    goal += goal_3.
    goal_3 += a_0(I,I).
    a_0(I,K) += b_1(I,J) * c_2(J,K).
    """)

    useful.assert_equal("""
    a(I,I) += a_0(I).
    b_1(I,J) += b(I,J).
    c_2(J,I) += c(J,I).
    goal += goal_3.
    goal_3 += a_0(I).
    a_0(K) += b_1(K,J) * c_2(J,K).
    """)


def test_startpath3():

    path = Program("""

    path(I,I).
    path(I,K) += path(I,J) * edge(J,K).

    inputs: edge(I,J).
    outputs: path(I,K).
    """)

    t = path.usefulness_analysis(
        input_type="""
        edge(I,J) :- n(I), n(J).

        inputs: start(I); n(I).
        """,
        output_type="""
        path(I,K) :- start(I), n(K).
        """,
    )
    t.assert_equal("""
    edge(J,K) += n(K) * n(J).
    path(I,J) += start(I) * n(I) * n(J).
    """)
    print('useful types', colors.mark(True))

    s = path.abbreviate(types=t)
    print(s)

    s.assert_equal("""
    path(I,J) += path_1(I,J).
    edge_0(J,K) += edge(J,K) * n(J) * n(K).
    path_1(I,I) += n(I) * start(I).
    path_1(I,K) += path_1(I,J) * edge_0(J,K).
    """)


def _todo_benchmarks():
    from dyna.benchmarks.collection import benchmark

    for name, b in benchmark.items():
        print()
        print(name)

        if name == 'chain-20':   # too slow
            print('skip')
            continue

        p = b.src
        #p = p.random_binarize()

        print(p)

        q = p.abbreviate().prune()

        if q.degrees() != p.degrees():
            print()
            print('change in degree!')
            print(name)
            print('was:', p.degrees())
            print('now:', q.degrees())
            print()

        out = b(q, 3, throw=True)
        if out == {}:
            print('no test case')
            continue   # no test case
        elif out['error']:
            print(colors.light.red % 'original', p)
            print('status:', colors.poop)
        else:

            # compare the number of prefix firings before and after transformation
            orig = b(p, 3, throw=True)

            new = out['prefix_firings']
            old = orig['prefix_firings']

            if new > old:
                print(f'relative pf: {new/old:.2f}x {colors.yellow % "slower"}')
            else:
                print(f'relative pf: {old/new:.2f}x {colors.white % "faster"}')

            new = out['wallclock']
            old = orig['wallclock']

            if new > old:
                print(f'relative wallclock: {new/old:.2f}x {colors.yellow % "slower"}')
            else:
                print(f'relative wallclock: {old/new:.2f}x {colors.white % "faster"}')

            print(colors.ok)


def test_example():

    p = Program("""
    goal += a(I,I).
    a(I,K) += b(I,J) * c(J,K).
    goal += dead(X).

    input: b(_,_); c(_,_).
    output: goal.
    """)

    t = p.usefulness_analysis()
    t.assert_equal("""
    a(I,I) :- $bound(I).
    b(I,J) :- $bound(I), $bound(J).
    c(J,I) :- $bound(I), $bound(J).
    goal.
    """)

    q = p.abbreviate(types=t)
    q.assert_equal("""
    a(I,I) += a_0(I).
    b_1(I,J) += b(I,J).
    c_2(I,J) += c(I,J).
    goal += goal_3.
    goal_3 += a_0(I).
    a_0(I) += b_1(I,J) * c_2(J,I).
    """)


def test_cancel():
    p = Program("""
    goal += f(X) * g(X).
    goal += f(X) * h(X).
    goal += g(X) * h(X).

    inputs: f(X); g(X); h(X).
    output: goal.
    """)

    t = p.type_analysis("""
    f(X) += a(X).
    g(X) += b(X).
    h(X) += c(X).
    inputs: a(X); b(X); c(X).
    """, """
    $fail += a(X), b(X).   % disjoint!
    """)

    q = p.abbreviate(types=t).prune_fast()
    q.assert_equal("""
    f_0(X) += f(X) * a(X).
    g_1(X) += g(X) * b(X).
    h_3(X) += h(X) * c(X).

    goal += goal_2.
    goal_2 += f_0(X) * h_3(X).
    goal_2 += g_1(X) * h_3(X).
    """)


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
