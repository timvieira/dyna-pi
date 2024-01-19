import numpy as np
from arsenal import colors, iterview
from dyna import Program, unifies, Symbol, Derivation
from dyna.term import NoDupsSet, fresh, Subst, unifies, covers, Var, vars, same


def vprime(x):
    return Subst({v: Var(v.name + "'") for v in vars(x)})(x)


def random_kwargs(P, xs=None):

    if xs is None:
        things = NoDupsSet([fresh(vprime(x)) for r in P for x in [r.head, *r.body]
                            if not P.is_const(x) and not P.is_input(x)], same)
        xs = list(things.xs)
    divisor = fresh(xs[np.random.choice(range(len(xs)))])

    # for each rule, we can slash at most one of its subgoals
    positions = {}
    for i,r in enumerate(P):
        positions[i] = np.random.choice(
            [None] + [
                j for j, b in enumerate(r.body)
                if not P.is_const(b) and not P.is_builtin(b)
                and (not unifies(b, divisor) or covers(divisor, b))
            ]
        )

    return dict(x=divisor, positions=positions)


# TODO: use more of this randomized stress test generator
def random_tests(P, D, q, want, reps=10, precision=4):
    # XXX: Stronger test: Check that all items in the original program P appear
    # with the same value in the transformed program Q.  The Q may define
    # additional items that do not appear in P.
    pd = P.solver2()(D).sol()
    pd.user_query(q).assert_equal(f'{q} += {want}.')

    for _ in range(reps):
        kwargs = random_kwargs(P)

        Q = P.lct(**kwargs).elim_p(0)

        qd = Q.solver2()(D).sol()

        sol = qd.user_query(q)
        sol.assert_equal(f'{q} += {want}.', precision=precision)
        print(f'[random spec] {colors.ok}')

        # Only p.outputs are guaranteed to be equal, but we can also check that
        # common items are equal.


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

    q = p.lct({0:0, 1:0, 2:0})
    print(q)
    check(q)
    q = q.prune()
    print(q)
    check(q)

    q = p.lct({0:0, 2:0})
    print(q)
    check(q)
    q = q.prune()
    print(q)
    check(q)


def test_other_other():

    p = Program("""
    a += y.
    a += z.

    a += a * x.

    inputs: x; y; z.
    outputs: a.
    """)

    D = """
    x += 0.5.
    y += 1.
    z += 1.
    """

    def check(p):
        d = (p+D).fc(1000)
        sol = d.user_query('a')
        sol.assert_equal('a += 4.')

    check(p)

    print('-----------------------------------------')

    print('slash:')
    q = p.slash('y', {0:0, 2:0}).prune()
    print(q)
    check(q)

    print('lct:')
    q = p.lct({0:0, 2:0}, x='y').prune()
    print(q)
    check(q)

    print('-----------------------------------------')

    print('lct:')
    q = p.lct({0:0, 2:0}, x='Y').prune()
    print(q)
    check(q)

    print('slash:')
    q = p.slash('Y', {0:0, 2:0}).prune()
    print(q)
    check(q)


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
        d = (p+D).agenda()
        sol = d.user_query('a')
        sol.assert_equal('a += 2.')

    check(p)

    q = p.lct({0:0,1:1})
    print(q)
    check(q)

    q = p.lct({1:1})
    print(q)
    check(q)

    q = p.lct({0:0})
    print(q)

    check(q)

    random_tests(p, D, 'a', 2)


def test_simple2():

    p = Program("""
    goal += x * y.
    goal += x * z.

    x += 2.
    y += 3.
    z += 4.
    """, inputs='', outputs='goal.')

    random_tests(P=p, D='', q='goal', want=14)


def test_acyclic():

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

    def check(p):
        d = p.solver2()(D)
        d.assert_equal_query('c', 24)
        d.assert_equal_query('a', 25)

    check(p)

    q = p.lct({0:1,2:0,3:2})
    check(q)

    for x in p.coarse_nodes():
        q = p.lct({0:1,2:0,3:2}, x=x)
        check(q)

    random_tests(P=p, D=D, q='a', want=25)


def test_cyclic():

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

    def check(p):
        d = p.solver2()(D)
        d.assert_equal_query('c', 64)
        d.assert_equal_query('a', 64)

    check(p)

    q = p.lct({0:1,1:0,2:2,3:1,4:0})
    check(q)

    for x in p.coarse_nodes():
        q = p.lct({0:1,1:0,2:2,3:1,4:0}, x=x)
        check(q)

    random_tests(P=p, D=D, q='a', want=64)


def test_cky_unary_cycle_factoring():
    #from dyna.benchmarks.cky import PAPA_DATA

    p = Program("""
    p(X,I,K) += rewrite(X,Y) * p(Y,I,K).
    p(X,I,K) += rewrite(X,Y,Z) * p(Y,I,J) * p(Z,J,K).
    p(X,I,K) += word(X,I,K).
    goal += length(N) * p("ROOT",0,N).

    inputs: rewrite(_,_,_); rewrite(_,_); word(_,_,_); length(_).
    output: goal.

    """)

    # Out of paranoia, check that the original program is correct.
    #p(PAPA_DATA).assert_equal_query('goal', 2)

    q = p.lct(positions={0: 1}, x="p(X',I',K')").prune()

    q.assert_equal("""
    (p($X3,$X1,$X2) / p($X3,$X1,$X2)).
    (p($X0,$X1,$X2) / p(Y,$X1,$X2)) += rewrite(X,Y) * p($X0,$X1,$X2) / p(X,$X1,$X2).
    $other(p(X,I,K)) += rewrite(X,Y,Z) * p(Y,I,J) * p(Z,J,K).
    $other(p(X,I,K)) += word(X,I,K).
    goal += length(N) * p("ROOT",0,N).
    p($X0,$X1,$X2) += $other(p($$X01,$X1,$X2)) * p($X0,$X1,$X2) / p($$X01,$X1,$X2).
    """)

    #q.solver2()(PAPA_DATA).assert_equal_query('goal', 2)


def test_growth():

    # deposit(Person): amount invested per year by person `Person`
    # rate(Prev, Year): rate of investment growth from year `Prev` to year `Year`
    # value(Person, Year): total value of investment in year `Year`

    p = Program("""
    value(Person, Year) += contributed(Year) * deposit(Person).
    value(Person, Year) += rate(Prev, Year) * value(Person, Prev).

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
        d = p.solver2()(D)
        d.assert_equal_query('value(maia, 3)', 2*(2*(2*(3)+3)+3)+3)
        d.assert_equal_query('value(hanna, 3)', 2*(2*(2*(2)+2)+2)+2)
        d.assert_equal_query('value(timv, 3)', 2*(2*(2*(1)+1)+1)+1)
        return d

    check(p)

    have = p.lct({0:1,1:1})

    # Inefficiency! This program will iterate over the full term of the
    # investment for every possible person `Person`

    # Below, is an example of the "speculation" transform where we have factored
    # the yearly growth from the specific person.

    print(have.prune())

    have.prune().assert_equal("""
    (value($X0,$X2) / value($X0,$X2)).
    (value($X0,$X1) / deposit($X0)) += contributed(Year) * value($X0,$X1) / value($X0,Year).
    (value($X0,$X1) / value($X0,Prev)) += rate(Prev,Year) * value($X0,$X1) / value($X0,Year).
    value($X0,$X1) += deposit($X0) * value($X0,$X1) / deposit($X0).
    """)

    check(have)

    import dyna
    dyna.gen_functor.reset()

    q = have.elim_p(0).abbreviate().prune()

    #if 0: q.assert_equal("""
    #value(Person, Year) += $inst_5(Person,Year).
    #$inst_4(Year) += contributed(Year).
    #$inst_4($X1) += contributed(Year) * $inst_3($X1,Year).
    #$inst_3(Year,Prev) += rate(Prev,Year).
    #$inst_3($X1,Prev) += rate(Prev,Year) * $inst_3($X1,Year).
    #$inst_5(Person,Year) += deposit(Person) * $inst_4(Year).
    #""")

    print(q)
    check(q)


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
        d.user_query('q(X)').assert_equal(want, precision=3)

    want = (p+D).sol().user_query('q(X)')

    # apply speculation to the inital state probability p(S).
    q = p.lct({0:1,1:2})

    #print(q)
    #check(q)
    print(q.prune())
    check(q.prune())

    # apply speculation to the inital state probability p(S).
    q = p.lct({0:1,1:2}, x='q(_)')
    #print(q)
    #check(q)
    print(q.prune())
    check(q.prune())

    print(q.prune().abbreviate().prune())
    check(q.prune().abbreviate().prune())


def test_diamond():
    p = Program("""
    b += a.
    c += 3 * a.
    d += a * c.
    """, inputs='a.', outputs='a. b. c. d.')

    # This diamond is non-linear, so the linear version of speculation transform
    # is currently not expected to work correctly.

    def check(src):
        D = 'a += 1.'
        d = (src + D).sol()
        want = {'a': 1, 'b': 1, 'c': 3, 'd': 3}
        for k,v in want.items():
            d.assert_equal_query(k, v)
        return d

    check(p)

    q = p.lct({0:0, 1:1, 2:1})
    check(q)
    check(q.prune())

    for x in p.coarse_nodes():
        q = p.lct({0:0, 1:1, 2:1}, x=x)
        check(q)
        check(q.prune())
        print(x)


def test_mutual_cycle():

    p = Program("""
    f += 0.5 * g.
    g += 0.5 * f.
    f += x.
    g += y.
    """, 'x. y.', 'f. g.')

    def check(p):
        d = (p+D).agenda()
        want = {'f': 2, 'g': 2}
        for k,v in want.items():
            d.user_query(k).assert_equal(f'{k} += {v}.')
        return d

    D = """
    x += 1.
    y += 1.
    """

    check(p)

    q = p.lct({0:1,1:1,2:0,3:0})
    check(q)

    for x in p.coarse_nodes():
        q = p.lct({0:1,1:1,2:0,3:0}, x=x)
        check(q)


def test_ryan_ccg():
    p = Program("""
    a += b.
    b += x.
    x += 2.
    """, inputs='', outputs='a. b.')

    def check(q):
        sol = q.solver2()()
        sol.assert_equal_query('a', 2)
        sol.assert_equal_query('b', 2)

    check(p)

    q = p.lct({0:0,1:0})

    for x in p.coarse_nodes():
        q = p.lct({0:0,1:0}, x=x)
        check(q)
        check(q.prune())


def test_slash_nonitem():
    p = Program("""
    goal += y.
    y += 13.

    outputs: goal.
    """)
    q = p.lct({0:0}, x='z')   # z is not in the program
    d = q.agenda()
    q.show_groundings(d)
    d.assert_equal_query('goal', 13)

#_______________________________________________________________________________
#

def test_derivation_mapping_left():

    p = Program("""
    w += x * `d`.
    x += y * `c`.
    y += z * `b`.
    z += `a`.

    outputs: w.
    """, semiring=Symbol)

    print(colors.yellow % colors.line(80))
    print(colors.yellow % 'parent derivations')
    P = p.derivations(10, 'w')
    P.render_terminal()
    assert len(P) == 1

    #print(colors.yellow % '-------------------------------------------------------')
    #print(colors.yellow % 'lct program')
    q = p.lct({0:0, 1:0, 2:0})
    #print(q)

    print(colors.yellow % colors.line(80))
    print(colors.yellow % 'lct derivations')
    Q = q.derivations(10, 'w')
    Q.render_terminal()

    for d in P:
        print(colors.yellow % colors.line(80))
        print(colors.yellow % 'transform:', d)
        D = q.transform(d)
        print(D.pp_proof())
        assert D in Q


def test_derivation_mapping1():

    # acyclic example
    p = Program("""
    a += b * `c`.
    b += `d`.

    outputs: a.
    """, semiring=Symbol)

    p = Program("""
    a += b * `c`.
    b += d * `e` * `h`.
    d += `f`.

    outputs: a.
    """, semiring=Symbol)

    print(colors.yellow % '-------------------------------------------------------')
    print(colors.yellow % 'lct program')
    q = p.lct({0:0, 1:0})
    print(q.prune())

    print(colors.yellow % '-------------------------------------------------------')
    print(colors.yellow % 'parent derivations')
    P = p.derivations(10, 'a')
    #P.render_terminal()
    for d in P:
        print(d)

    print(colors.yellow % '-------------------------------------------------------')
    print(colors.yellow % 'lct derivations')
    Q = q.derivations(10, 'a')
    #Q.render_terminal()

    for d in Q:
        print(d)

    assert len(P) == len(Q)

    failed = False
    for d in P:
        print(colors.yellow % '----------------------------')
        print(colors.yellow % 'transform:', d)
        #print(d.pp_proof())

        D = q.transform(d)
        #print(D.pp_proof())
        print(D)
        #assert D in Q
        if D not in Q:
            failed = True
        print(colors.mark(D in Q), 'derivation exists in q')
        print(colors.mark(D.value() == d.value()), 'value preserved')

    assert not failed


if __name__ == '__main__':
    from arsenal.testing_framework import testing_framework
    testing_framework(globals())
