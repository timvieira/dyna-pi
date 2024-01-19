import numpy as np
from arsenal import colors, iterview, timelimit
from collections import defaultdict

from dyna import Program, NoDupsSet, fresh, Subst, unifies, covers, Var, vars, same, Symbol
#from dyna.transform.slash_enum import random_kwargs


def vprime(x):
    return Subst({v: Var(v.name + "'") for v in vars(x)})(x)


def random_args(P, xs=None, prune=False):

    if xs is None:
        things = NoDupsSet([fresh(vprime(x)) for r in P for x in [r.head, *r.body] if not P.is_const(x)], same)
        xs = list(things.xs)
    divisor = fresh(xs[np.random.choice(range(len(xs)))])

    if prune:
        g = Graph(P)

    # for each rule, we can slash at most one of its subgoals
    positions = {}
    for i,r in enumerate(P):
        positions[i] = np.random.choice(
            [None] + [
                j for j, b in enumerate(r.body)
                if not P.is_const(b) and not P.is_builtin(b)
                and (not unifies(b, divisor) or covers(divisor, b))
                and (not prune or g.depends_on_x(g.node(b), g.node(divisor)))
            ]
        )

    return (divisor, positions)


def test_slash_const():

    p = Program("""
    a += 1.
    a += 2.

    a += a * x.

    inputs: x.
    outputs: a.
    """)

    D = """
    x += 0.5.
    """

    def check(p):
        d = (p+D).fc()
        sol = d.user_query('a')
        sol.assert_equal('a += 6.')

    check(p)

    q = p.slash('X', {0:0, 1:0, 2:0})
    print(q)
    check(q)
    q = q.prune()
    print(q)
    check(q)

    q = p.slash('X', {0:0, 2:0})
    print(q)
    check(q)
    q = q.prune()
    print(q)
    check(q)


def test_derivation_mapping_simple1():

    # acyclic example
    p = Program("""
    a += b * c.
    a += c.
    b += `r`.
    c += `d` * `e` * x.
    x += `f`.

    outputs: a; c.
    """)


    P = p.derivations(10, 'a')
    #P.render_terminal()

    #print(colors.yellow % '-------------------------------------------------------')
    q = p.slash('x', {0:1, 1:0, 3:2})
    #print(q)

    #print(colors.yellow % '-------------------------------------------------------')
    Q = q.derivations(10, 'a')
    #Q.render_terminal()

    for d in P:
        #print(colors.yellow % '----------------------------')
        #print(colors.yellow % 'transform:', d)
        D = q.transform(d)
        #print(D.pp_proof())
        assert D in Q


def test_derivation_mapping_simple2():

    p = Program("""
    a += b * c.
    b += `r`.
    c += `d` * `e` * x.
    c += `f` * c.          % <=== cyclic rule
    c += `g`.
    x += `m`.

    outputs: a; c.
    """)

    P = p.derivations(5, 'a')
    #P.render_terminal()

    #print(colors.yellow % '-------------------------------------------------------')
    #print(colors.yellow % 'slash program')
    q = p.slash('x', {0:1, 2:2})
    #print(q)

    #print(colors.yellow % '-------------------------------------------------------')
    #print(colors.yellow % 'slash derivations')
    Q = q.derivations(10, 'a')
    #Q.render_terminal()

    #print(colors.yellow % '-------------------------------------------------------')
    #print(colors.yellow % 'derivations mapping')

    for d in P:
        #print(colors.yellow % 'transform:', d)
        D = q.transform(d)
        #print(D.pp_proof())
        assert D in Q


def test_geom():

    p = Program("""
    a += y.
    a += a * x.
    inputs: x; y.
    outputs: a.
    """)

    D = """
    x += 0.5.
    y += 1.
    """

    def check(p):
        d = p(D)
        sol = d.user_query('a')
        sol.assert_equal('a += 2.')

    check(p)

    q = p.slash('x', {0:0, 1:1})
    q.tidy().assert_equal("""
    (a / x) += a.
    a += a / x * x.
    a += y.
    """)
    check(q)

    random_speculation_tests(p, D, 'a', 2)


def test_spec_simple():

    p = Program("""
    goal += x * y.
    goal += x * z.
    """, inputs='x.y.z.', outputs='goal.')

    D = """
    x += 2.
    y += 3.
    z += 4.
    """

    p.slash('x', positions={0: 0, 1: 0}).tidy().assert_equal("""
    (goal/x) += y.
    (goal/x) += z.
    goal += (goal/x) * x.
    """)

    # The slash operation below is a no-op (after tidying) because it does not
    # manage to hoist an `x` up from `goal`.
    q = p.slash('x', positions={0: 1, 1: 1})
    q.tidy().assert_equal("""
    goal += x * y.
    goal += x * z.
    """)

    random_speculation_tests(P=p, D=D, q='goal', want=14)


def test_spec_acyclic():

    # acyclic example
    p = Program("""
    a += b * c.
    a += 1.
    b += r.
    c += d * e * x.   % fold x in this rule
    """, 'x. r. d. e.', 'a. c.')

    D = """
    x += 4.
    r += 1.
    d += 2.
    e += 3.
    """

    def check(p, D):
        d = p(D)
        d.assert_equal_query('c', 24)
        d.assert_equal_query('a', 25)
        return d

    check(p, D)

    q = p.slash('x', {0:1, 2:0, 3: 2})

    q.prune().assert_equal("""

    (a / x) += b * c / x.
    (c / x) += d * e * x / x.
    (x / x).
    c += c / x * x.
    a += a / x * x.

    a += 1.
    b += r.

    """)
    check(q, D)

    random_speculation_tests(P=p, D=D, q='a', want=25)


def test_spec_cyclic():

    p = Program("""
    a += b * c.
    b += r.
    c += d * e * x.
    c += f * c.          % <=== cyclic rule
    c += g.
    """, 'r.d.e.x.f.g.', 'a. c.')

    D = """
    r += 1.
    d += 2.
    e += 3.
    x += 4.
    f += 0.5.
    g += 8.0.
    """

    def check(p,D):
        d = p(D)
        d.user_query('c').assert_equal('c += 64.')
        d.user_query('a').assert_equal('a += 64.')

    check(p, D)

    q = p.slash('x', {0:1, 1:0, 2:2, 3:1, 4:0})

    q.prune().assert_equal("""
    (x / x).
    (a / x) += b * c / x.
    (c / x) += d * e * x / x.
    (c / x) += f * c / x.
    a += b * $other(c).
    b += r.
    $other(c) += f * $other(c).
    $other(c) += g.
    a += a / x * x.
    c += c / x * x.
    c += $other(c).
    """)

    check(q, D)

    random_speculation_tests(P=p, D=D, q='a', want=64)


def test_cky_unary_cycle_factoring():
    #from dyna.benchmarks.cky import PAPA_DATA

    # XXX: The Papa grammar is a largely useless test of this transform because
    # there are no unary chains!

    p = Program("""
    p(X,I,K) += rewrite(X,Y) * p(Y,I,K).
    p(X,I,K) += rewrite(X,Y,Z) * p(Y,I,J) * p(Z,J,K).
    p(X,I,K) += word(X,I,K).
    goal += length(N) * p("ROOT",0,N).
    """, inputs='rewrite(_,_,_). rewrite(_,_). word(_,_,_). length(_).',
                outputs='goal.')

    # Out of paranoia, check that the original program is correct.
#    p(PAPA_DATA).assert_equal_query('goal', 2)

    # Check that the generated code matches
    q = p.slash("p(X',I',K')", positions={0: 1}).prune()
    print(q)

    # Matches "the slashed notation is not merely expository..."
    q.assert_equal("""
    (p(X0,I0,K0)/p(X0,I0,K0)).
    (p(X,I0,K0)/p(X0,I0,K0)) += rewrite(X,Y) * p(Y,I0,K0)/p(X0,I0,K0).
    $other(p(W,I,K)) += word(W,I,K).
    $other(p(X,I,K)) += rewrite(X,Y,Z) * p(Y,I,J) * p(Z,J,K).
    p(X,I0,K0) += (p(X,I0,K0)/p(X0,I0,K0)) * $other(p(X0,I0,K0)).

%    goal += $other(goal).
%    $other(goal) += length(N) * p("ROOT", 0, N).

    goal += length(N) * p("ROOT", 0, N).
    """)

    # Run nonground forward chaining
#    ddd = q.solver2()(PAPA_DATA)
#    ddd.user_query('goal').assert_equal('goal += 2.')

    #___________________________________________________________________________
    # Below is an attempt to massage the program into a Datalog-like form

    #q = q.introduce("tmp(X,X') += p(X,I,K) / p(X',I',K').")
    #q = q.prune()

    # we manage to get this subprogram
    # tmp(X',X') += 1.
    # tmp(X,X') += tmp(Y,X') * rewrite(X,Y).
    #
    # However, it does not integrate with the remaining program (it is a useless
    # appendage that pruning will eliminate).
    #
    # The tricky rule is this one
    #   p(X,I,K) += p(X,I,K) / p(X',I',K') * other(p(X',I',K')).
    #
    # It needs to become
    #   p(X,I,K) += tmp(X,X')*other(p(X',I,K)).

    # Unfortunately, the "bad vars" condition means that we can't apply our CSE
    # Somehow, we need to make I'=I and K'=K.
    #
    # This analysis works bottom-up.  Essentially, we have to figure out from
    # the program that only items with I'=I and K'=K are supported.
    #
    # cse(X", I", K") += p(X", I", K") / p(X', I", K") * other(p(X', I", K").

    #q.assert_equal("""
    #tmp(X',X') += 1.
    #tmp(X,X') += tmp(Y,X') * rewrite(X,Y).
    #p(X,I,K) += tmp(X,X') * other(p(X',I,K)).
    #
    #other(p(X,I,K)) += rewrite(X,W) * word(W,I,K).
    #other(p(X,I,K)) += rewrite(X,Y,Z) * p(Y,I,J) * p(Z,J,K).
    #
    #goal += other(goal).
    #other(goal) += length(N) * p("ROOT", 0, N).
    #
    #% annoying extra rules
    #length($X') += other(length($X')).
    #rewrite($X', $X1, $X2) += other(rewrite($X', $X1, $X2)).
    #rewrite($X', $X1) += other(rewrite($X', $X1)).
    #word($X', $X1, $X2) += other(word($X', $X1, $X2)).
    #
    #""")


def test_growth():

    # deposit(Person): amount invested per year by person `Person`
    # rate(Prev, Year): rate of investment growth from year `Prev` to year `Year`
    # value(Person, Year): total value of investment in year `Year`

    # XXX: if contributed(Year) is boolean.
    p = Program("""
    value(Person, Year) += contributed(Year) * deposit(Person).
    value(Person, Year) += value(Person, Prev) * rate(Prev, Year).
    inputs: deposit(_); rate(_,_); contributed(_).
    outputs: value(_,_).
    """)

    D = """
    deposit(timv)  += 1.
    deposit(hanna) += 2.
    deposit(maia)  += 3.

    rate(0,1) += 2.
    rate(1,2) += 2.
    rate(2,3) += 2.

    contributed(0) += 1.
    contributed(1) += 1.
    contributed(2) += 1.
    contributed(3) += 1.
    """

    def check(p):
        d = p(D)
        d.assert_equal_query('value(maia, 3)', 2*(2*(2*(3)+3)+3)+3)
        d.assert_equal_query('value(hanna, 3)', 2*(2*(2*(2)+2)+2)+2)
        d.assert_equal_query('value(timv, 3)', 2*(2*(2*(1)+1)+1)+1)
        return d

    check(p)

    have = p.slash('deposit(Person)', {0:1,1:1})

    # Inefficiency! This program will iterate over the full term of the
    # investment for every possible person `Person`

    # Below, is an example of the "speculation" transform where we have factored
    # the yearly growth from the specific person.

    check(have.solver2())

    have.prune().assert_equal("""
    (deposit(Person) / deposit(Person)) += 1.0.
    (value(Person,Year) / deposit(Person)) += contributed(Year) * deposit(Person) / deposit(Person).
    value(Person,Prev) += deposit(Person) * value(Person,Prev) / deposit(Person).
    value(Person,Prev) += value(Person,$Prev1) * rate($Prev1,Prev).
    """)


def test_power_iteration():

    p = Program("""
    q(S) += 0.1 * p(S).
    q(S') += 0.9 * p2(S',S) * q(S).
    """, inputs="p(S). p2(S',S).", outputs='q(_).')

    D = """
    p(a)    += 0.75.
    p(b)    += 0.25.
    p2(a,a) += 0.6.
    p2(b,a) += 0.4.
    p2(a,b) += 0.5.
    p2(b,b) += 0.5.
    """

    def check(p):
        d = p.solver2()(D)
        d.user_query('q(X)').assert_equal("""
        q(a) += 0.57692.
        q(b) += 0.42307.
        """)

    check(p)

    # apply speculation to the inital state probability p(S).
    q = p.slash("p(S')", {0:1, 1:2}).prune()
    print(q)
    q.assert_equal("""
    (p(S') / p(S')).
    (q(S') / p(S')) += 0.1 * p(S') / p(S').
    (q(S') / p($S'1)) += 0.9 * p2(S',S) * q(S) / p($S'1).
    q(S) += p(S') * q(S) / p(S').
    """)
    check(q)



def test_diamond():
    p = Program("""
    b += a.
    c += 3 * a.
    d += a * c.
    """, inputs='a.', outputs='a. b. c. d.')

    # This diamond is non-linear, so the linear version of speculation transform
    # is currently not expected to work correctly.

    def check(src):
        d = (src + 'a += 1.').solve()

        want = {'a': 1, 'b': 1, 'c': 3, 'd': 3}
        for k,v in want.items():
            d.assert_equal_query(k, v)

        return d

    check(p)
    q = p.slash('a', {0:0, 1:1, 2:1})
    check(q)
    check(q.prune())

    q = p.slash('a', {0:0, 1:1, 2:1}).prune()
    q.assert_equal("""
    (a / a) += 1.0.
    (b / a) += a / a.
    (c / a) += 3.0 * a / a.
    (d / a) += a * c / a.
    b += b / a * a.
    c += c / a * a.
    d += d / a * a.
    """)
    check(q)
    check(q.prune())


def test_mutual_cycle():

    p = Program("""
    f += 0.5 * g.
    g += 0.5 * f.
    f += x.
    g += y.
    """, 'x. y.', 'f. g.')

    def check(p, D):

        d = p(D)

        want = {'f': 2, 'g': 2}
        for k,v in want.items():
            d.user_query(k).assert_equal(f'{k} += {v}.')
        return d

    D = """
    x += 1.
    y += 1.
    """

    check(p, D)

    q = p.slash('x', {0:1,1:1,2:0,3:0}).prune()

    q.assert_equal("""
    (x / x).
    (f / x) += 0.5 * g / x.
    $other(f) += 0.5 * $other(g).
    (g / x) += 0.5 * f / x.
    $other(g) += 0.5 * $other(f).
    (f / x) += x / x.
    $other(g) += y.
    f += f / x * x.
    f += $other(f).
    g += g / x * x.
    g += $other(g).
    """)

    check(q, D)


def test_ryan_ccg():
    p = Program("""
    a += b.
    b += x.
    x += 2.
    """, inputs='', outputs='a. b.')

    d1 = p()
    d1.assert_equal_query('a', 2)
    d1.assert_equal_query('b', 2)

    q = p.slash('x', {0:0, 1:0}).prune()

    q.assert_equal("""
    (x / x) += 1.0.
    (a / x) += b / x.
    (b / x) += x / x.
    $other(x) += 2.0.
    a += a / x * $other(x).
    b += b / x * $other(x).
    """)

    d2 = q()
    d2.assert_equal_query('a', 2)
    d2.assert_equal_query('b', 2)


def test_slash_nonitem():
    p = Program("""
    goal += y.
    y += 13.
    """, inputs='', outputs='goal.')
    q = p.slash('z', {0:0}).prune()   # z is not in the program
    d = q()
    d.assert_equal_query('goal', 13)


#_______________________________________________________________________________
# Randomized speculation stress tests

# TODO: use more of this randomized stress test generator
def random_speculation_tests(P, D, q, want, reps=10, precision=4):
    # XXX: Stronger test: Check that all items in the original program P appear
    # with the same value in the transformed program Q.  The Q may define
    # additional items that do not appear in P.

    # Note that the lack of full-consolidation in solver2 affects this comparison.
#    pd = P.solver2()(D).sol()

    for _ in range(reps):

        args = random_args(P)
        Q = P.slash(*args).tidy()

        qd = Q.solver2()(D).sol()

#        ps = P.get_syms()
#
#        #pd.compare(qd)
#        for r,s in pd.align(qd):
#            # ok to not match s because we can define new items in the
#            # transformed program
#            if r is None:
#                assert s.head.fn not in ps
#                assert not P.is_output(s.head), [r,s]
#                #print('new q rule:', s)
#            elif s is None:
#                assert not P.is_output(r.head), [r,s]
#                #assert False, 'here is the example you have been looking for ^^^'
#            else:
#                assert r.same(s)
#            #print(r, s)

        sol = qd.user_query(q)
        sol.assert_equal(f'{q} += {want}.', precision=precision)
        print(f'[random spec] {colors.ok}')

        a = Q.abbreviate()
        A = a(D)
        sol = A.user_query(q)
        sol.assert_equal(f'{q} += {want}.', precision=precision)
        print(f'[random spec+abbrev] {colors.ok}')


# XXX: work in progress
def test_bilexical():
    p = Program("""

    % 0 right children so far
    rconstit(X:H,I,K) += rewrite(X,H) * word(H,I,K).

    % add right child
    rconstit(X:H,I,K) += rewrite(X:H,Y:H,Z:H2) * rconstit(Y:H,I,J) * constit(Z:H2,J,K).

    % 0 left children so far
    constit(X:H,I,K) += rconstit(X:H,I,K).

    % add left child
    constit(X:H,I,K) += rewrite(X:H,Y:H2,Z:H) * constit(Y:H2,I,J) * constit(Z:H,J,K).

    % goal
    goal += constit(s:H,0,N) * length(N).

    inputs: length(_); rewrite(_,_,_); rewrite(_,_); word(_,_,_).
    outputs: goal.
    """)

    input_type = Program("""
    rewrite(X:H,Y:H,Z:H2) :- w(H), w(H2), k(X), k(Y), k(Z).
    rewrite(X,H) :- w(H), k(X).
    length(N) :- n(N).
    word(H,I,K) :- w(H), n(I), n(K).

    inputs: w(_); k(_); n(_).
    """)

    S = p.type_analysis(input_type, """
    k(s).
    n(0).
    """)
    print(S)

    x = Program('rconstit(X0:H0,I0,K0).').rules[0].head
    q = p.slash(x, positions={2:0, 3:2})

    q = q.prune()

    print(q)

    S = q.type_analysis(input_type, """
    k(s).
    n(0).
    """)
    print(S)

#    want = Program("""
#    (rconstit(X0:H0,J0,K0)/rconstit(X0:H0,J0,K0)).
#    (constit(X:H,J,K)/rconstit(X0:H0,J0,K0))
#      += rconstit(X:H,J,K)/rconstit(X0:H0,J0,K0).
#    (constit(X:H,I,K)/rconstit(X0:H0,J0,K0)) += rewrite(X:H,Y:H2,Z:H) * constit(Y:H2,I,J)
#      * constit(Z:H,J,K)/rconstit(X0:H0,J0,K0).
#    constit(X:H,I,K) += constit(X:H,I,K)/rconstit(X0:H0,J0,K0) * rconstit(X0:H0,J0,K0).
#
#    % old rules
#    rconstit(X:H,I,K) += rewrite(X,H) * word(H,I,K).
#    rconstit(X:H,I,K) += rewrite(X:H,Y:H,Z:H2) * rconstit(Y:H,I,J) * constit(Z:H2,J,K).
#    goal += constit(s:H,0,N) * length(N).
#
#    inputs: length(_); rewrite(_,_,_); rewrite(_,_); word(_,_,_).
#    outputs: goal.
#    """)
#    q.compare(want)

    q.show_analyzers()
    print(q.degrees())

#    from IPython import embed; embed()



def test_derivation_mapping_speculation():

    for cfg in [

            Program("""

            s += `a` * `b` * `c`.

            output: s.

            """, semiring=Symbol),

            Program("""

            s += a * `c`.
            a += `a`.
            a += `b`.

            output: s.

            """, semiring=Symbol),

            Program("""

            s += s1 * `a`.
            s1 += d.
            s1 += e.
            d += `d`.
            e += `e`.

            output: s.
            """, semiring=Symbol),

            Program("""

            s += s1 * `a1`.
            s1 += s2 * `a2`.
            s2 += s3 * s3.
            s3 += s4.
            s4 += a * `a4`.
            s4 += c * `a4`.
            c += `c`.

            outputs: s.

            """, semiring=Symbol),

            Program("""

            s += s(0).
            s(0) += s(1) * s(1).
            s(1) += s(2) * s(2).
            s(2) += s(3) * `d`.
            s(3) += `a`.
            s(3) += `b`.

            outputs: s.

            """)
    ]:

        T = 12
        src = list(cfg.derivations(T, 's'))

        if 1:
            print(colors.line(80))

            sp = cfg.slash('X', {})
            tgt = list(sp.derivations(T, 's'))
            _test_derivation_mapping(sp, src, tgt)

        if 1:
            print(colors.line(80))

            sp = cfg.slash('X', {i: 0 for i in range(len(cfg))})
            tgt = list(sp.derivations(T, 's'))
            _test_derivation_mapping(sp, src, tgt)


        if 1:
            print(colors.line(80))

            sp = cfg.slash('d', {i: 0 for i in range(len(cfg))})
            tgt = list(sp.derivations(T, 's'))
            _test_derivation_mapping(sp, src, tgt)


def _test_derivation_mapping(q, src, tgt):
    f = q.transform

    assert len(src) == len(tgt)
    print(colors.yellow % 'Source Derivations:')
    for t in src:
        print(' ', t)

    print(colors.yellow % 'Target Derivations:')
    for t in tgt:
        print(' ', t)

    print(colors.yellow % 'Forward Mapping:')
    ok = True
    mapsto = defaultdict(list)
    for t in src:
        print(colors.orange % ':', t)
        ft = f(t)
        print(colors.mark(ft in tgt), ft)
        ok &= (ft in tgt)
        mapsto[ft].append(t)

        assert t.value() == ft.value()
        assert t.head == ft.head

    assert all(len(mapsto[ft]) == 1 for ft in tgt)
    assert ok



if __name__ == '__main__':
    from arsenal.testing_framework import testing_framework
    testing_framework(globals())
