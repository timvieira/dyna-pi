import z3
import dyna
import sympy
from arsenal import colors
from dyna import Program, Boolean
from dyna.transform.measure import make_smt_measure as make_measure, Interval


class analyze_predictions:
    "Compute quantities: precision, recall, accuracy, tp, fp, fn, tn."
    def __init__(self, xs, want, have):
        tp = 0; fp = 0; fn = 0; tn = 0
        for x in xs:
            if x in want:
                if x in have:
                    tp += 1
                else:
                    fn += 1
            else:
                if x in have:  # pragma: no cover
                    fp += 1
                else:
                    tn += 1
        self.precision = tp/(tp+fp) if (tp+fp) > 0 else 1
        self.recall = tp/(tp+fn) if (tp+fn) > 0 else 1
        self.accuracy =  (tp+tn)/(tp+tn+fp+fn)
        self.tp = tp
        self.fp = fp
        self.tn = tn
        self.fn = fn

    def __repr__(self):
        tp = self.tp; fp = self.fp; tn = self.tn; fn = self.fn
        P = lambda x,y: f'{x/y:.1%} ({x}/{y})' if y > 0 else '100% (0/0)'
        return f"""\
precision: {P(tp, tp+fp)}
recall:    {P(tp, tp+fn)}
accuracy:  {P(tp+tn, tp+tn+fp+fn)}\
"""


class compare(analyze_predictions):
    def __init__(self, ref, xs, m, D='', sol=None, verbose=False):
        assert len(xs) > 0
        if sol is None: sol = (ref+D).sol().round(precision=3)
        have = set(); want = set()
        for x in xs:
            correct = ((x+D).sol().round(precision=3) == sol)
            safe = m(x)
            if verbose: print(colors.mark(correct), colors.mark(safe), x)
            if correct: want.add(x)
            if safe: have.add(x)
        assert len(want) > 0
        self.have = have
        self.want = want

        self.ref = ref
        self.sol = sol
        self.xs = xs
        self.D = D
        self.m = m

        super().__init__(xs, have=have, want=want)
        if verbose: print(self)


def test_startpath():

    p = Program("""
    goal += startpath(K) * stop(K).
    path(I,K) += 1.
    path(I,K) += path(I,J) * w(J,K).

    startpath(K) += start(I) * path(I,K).

    inputs: start(_); w(_,_); stop(_).
    outputs: goal.

    """)

    m = make_measure(p)
    print(m(p))

    q = p.unfold(3, 1)
    print(m(q))

    target = Program("""
    startpath(K) += startpath(J) * w(J,K).
    goal += startpath(K) * stop(K).
    startpath(K) += start(I) * 1.
    """)

    assert target in p.unfolds().partial_megafolds(p).filter(m.safe).prune()

    x = q.partial_megafolds(p).filter(m.safe).min(key = lambda x: x.prune().degrees())
    print(colors.yellow % 'unpruned:', m(x))
    print(m(x)._safe)
    print(z3.simplify(z3.And(*m(x)._safe)))

    print(colors.light.green % 'success!', x.prune())
    assert x.prune() == target, x.prune()


def test_evenodd_peano():

    P = Program("""
    goal += strange(X).

    strange(X) += even(X) * even(s(X)).

    even(0).
    even(s(s(X))) += even(X).

    outputs: goal.

    """)

    print('original defs:')

    m = make_measure(P)

    print(m(P))

    print('\nfold me:')
    Q = P.unfold(1, 1)
    print(m(Q))

    print('\n== Candidates ================')
    found = False
    for new in Q.partial_megafolds(P).filter(m.safe):
        new_p = new.prune()
        if new_p == "":
            print(colors.light.green % 'FOUND!')
            found = True
            print('prior to pruning:', new)
        print(colors.yellow % '=prune=>', new_p)
    assert found


def test_evenodd_list():

    P = Program("""
    even([]).
    even([X1,X2|Xs]) += even(Xs).
    goal += even([X|Xs]) * even(Xs).

    outputs: goal.
    """, semiring=Boolean)

    def search(p0):
        p0 = p0.reset_transform_history()
        m = make_measure(p0)
        ps = p0.partial_megafolds().unfolds().partial_megafolds(p0).dedup().filter(m.safe)
        for p3 in ps:   # pragma: no branch
            p4 = p3.prune(specialize=False, max_depth=3)
            if p4 == "":
                return p3

    a = P.define('strange([X|Xs]) += even([X|Xs]) * even(Xs).').reset_transform_history()
    found = search(a)
    print(found)
    assert found.prune() == ''
    print('success:', colors.mark(True))


def test_simple():

    # TODO: test case. replicate the old fold with define+generalizedfold; make sure
    # that the safety condition always passes.  I suspect it might very annoying
    # fail on
    #   goal += f(X) * g(X).
    # fold(0,[0,1])
    #   goal += tmp
    #   tmp += f(X) * g(X).
    # because there is no "extra" term.
    # that said, this fold is reversible, so there is a different means for accepting it.
    #
    # We can apparently break the measure-based safety check by multiplying
    # each rule by some number of 1s.

    p0 = Program("""
    goal += f(X).
    goal += 1.

    tmp += f(X).

    inputs: f(_).
    outputs: goal.
    """)

    target = Program("""
    goal += tmp.
    goal += 1.
    tmp += f(X).

    inputs: f(_).
    outputs: goal.
    """)

    assert p0.reversible_megafolds() == [target]
    print('reversible:', colors.ok)

    assert p0.partial_megafolds(p0) == [target]

    m = make_measure(p0)
    for x in p0.partial_megafolds(p0):
        print(m(x))
    have = p0.partial_megafolds(p0).filter(m.safe)
    assert have == [target], have

    print(colors.ok)


def test_geom():

    p0 = Program("""
    x += b.
    x += a * x.

    inputs: a; b.
    outputs: x.
    """)

    m = make_measure(p0)
    #print(colors.light.green % colors.rightarrow, m(p0))

    p1 = p0.unfold(1, 1, defs=p0)
    p1.assert_equal("""
    x += b.
    x += a * b.
    x += a * a * x.
    """)

    p2 = p1.unfold(2, 2, defs=p0)
    p2.assert_equal("""
    x += b.
    x += a * b.
    x += a * a * b.
    x += a * a * a * x.
    """)

    D = 'b += 3. a += 0.5.'

    #print('MANUAL FOLD:', end=' ')
    #qq = p2.basic_fold(p2.parent[p2.i], p2.j, p2.new2def, defs=p0)
    #qq.assert_equal(p1)
    #print(colors.ok)
    #print(m(qq))

    A = compare(p0, set(p2.partial_megafolds(p0)), m=m.safe, D=D)
    print(A)
    assert A.accuracy == 1
    assert len(A.want) == 1
    for x in p2.partial_megafolds(p0):
        print(m(x))

    A = compare(p0, set(p1.partial_megafolds(p0)), m=m.safe, D=D)
    print(A)
    assert A.accuracy == 1
    assert len(A.want) == 1
    for x in p1.partial_megafolds(p0):
        print(m(x))

    A = compare(p0, {y for x in p2.partial_megafolds(p0) for y in x.partial_megafolds(p0)},
                m=m.safe, D=D)
    print(A)
    assert A.accuracy == 1
    assert len(A.want) == 1
    for x in p2.to_collection().partial_megafolds(p0).partial_megafolds(p0).dedup():
        print(m(x))

    print(colors.ok)


def test_abcd1():

    p0 = Program("""
    goal += a * b * c * d.
    ab += a * b.
    cd += c * d.
    """)

    D = 'a += 2. b += 3. c += 5. d += 7.'

    #print(p0.coarse_nodes())
    #print(p0.coarse_hypergraph().graphviz().open())

    m0 = make_measure(p0)
    print('init:', m0(p0))

    p1 = p0.partial_megafolds()[0]
    print(m0(p1))

    p2 = p1.partial_megafolds(p0)[0]
    print(m0(p2))

#    print(m(p1))
#    print(m(p1.partial_megafolds()[0]))

#    assert len(p1.partial_megafolds(p0)) == 1
#    assert len(p1.partial_megafolds()) == 1

#    assert len(p1.reversible_megafolds(p0)) == 1
#    assert len(p1.reversible_megafolds()) == 1

#    assert len(list(filter(m0.safe, p1.partial_megafolds()))) == 1
#    assert len(list(filter(m0.safe, p1.partial_megafolds(p0)))) == 1

    print()
    a = compare(p0, set(p1.partial_megafolds(p1)), m0.safe, D=D)
    print(a)
    assert a.precision == 1
    assert a.recall == 1

    print()
    a = compare(p0, set(p1.partial_megafolds(p0)), m0.safe, D=D)
    print(a)
    assert a.precision == 1
    assert a.recall == 1

    # take measures to be relative to p1
    m1 = make_measure(p1)
    print(m1(p0))   # should be completely uncertain because p0 is out of range

    for x in p1.partial_megafolds(p1):
        print('----')
        print(m0(x))
        print(m1(x))

    for x in p1.partial_megafolds(p0):
        print('----')
        print(m0(x))
        print(m1(x))

    print()
    a = compare(p0, set(p1.partial_megafolds(p1)), m1.safe, D=D)
    print(a)
    assert a.precision == 1

    print()
    a = compare(p0, set(p1.partial_megafolds(p0)), m1.safe, D=D)
    print(a)
    assert a.precision == 1

#    assert len(list(filter(m1.safe, p1.partial_megafolds(p1)))) == 1
#    assert len(list(filter(m1.safe, p1.partial_megafolds(p0)))) == 0   # should fail


def test_abcdef():
    p0 = Program("""
    goal += a * b * c * d * e * f.
    ab += a * b.
    cd += c * d.
    ef += e * f.

    inputs: a;b;c;d;e;f.
    outputs: goal.
    """)

    m = make_measure(p0)
    print(m(p0))

    p1 = p0.partial_megafolds(p0)[0]
    print(m(p1))
    assert m(p1).is_safe()

    p2 = p1.partial_megafolds(p0)[0]
    print(m(p2))
    assert m(p2).is_safe()

    p3 = p2.partial_megafolds(p0)[0]
    print(m(p3))
    assert m(p3).is_safe()


def test_pq1():

    p = Program("""
    p += 1.
    q += 1.
    """)

    want = {
        Program("p += q. q += 1."),
        Program("p += 1. q += p."),
    }

    m = make_measure(p)
    print(colors.light.green % colors.rightarrow, m(p))

    have = set()
    for x in p.partial_megafolds(p, skip_trivial=False):
        print(m(x))
        if m(x).is_safe():
            have.add(x)

    assert have <= want
    assert have == want


# TODO: this test is incomplete
def test_pq2():

    p0 = Program("""
    p += 1.
    q += 1.
    """)

    m = make_measure(p0)

    pool = p0.to_collection().partial_megafolds(p0).partial_megafolds(p0).dedup()

    assert len(pool) == 4

    for x in pool:
        print(m(x))

    # ideally, of the the 4 programs in the pool, we would identify 3 safe and 1 unsafe
    assert len(pool.filter(m.safe)) == 3


def test_bad_unfold_v1():

    s = Program("""
    p += q.
    q += r.
    r += 1.
    """)

    m = make_measure(s)

    target = Program("""
    p += 1.
    q += r.
    r += p.
    """)

    flat = s.unfold(0,0).unfold(0,0).unfold(1,0)

    flat.assert_equal("""
    p += 1.
    q += 1.
    r += 1.
    """)
    #print(m(flat))

    [d] = flat.partial_megafolds(None).partial_megafolds(None).dedup().filter(target.same)

    print(m(s))
    print(m(d))

    s.sol().assert_equal(d.sol())

    print(colors.light.yellow % 'bad unfold:')
    t = s.unfold(1,0,defs=d)
    t.undo.assert_equal(s)
    assert t - t.undo.S + t.undo.r == s
    print(m(t))
    assert t.sol() != s.sol()

    assert not m(t).is_safe()

    print(colors.light.yellow % 'all unfolds:')
    a = compare(s, set(s.unfolds(d)), m=m.safe)
    print(a)
    assert a.accuracy == 1


def test_bad_unfold_v2():

    s = Program("""
    p += q.
    q += r.
    r += 1.
    """)

    g = s.to_collection()


    target = Program("""
    p += 1.
    q += r.
    r += p.
    """)

    flat = g.add(g.add(g.add(s.unfold(0,0)).unfold(0,0)).unfold(1,0))

    flat.assert_equal("""
    p += 1.
    q += 1.
    r += 1.
    """)
    #print(m(flat))

    found = None
    for x in flat.partial_megafolds():
        for y in x.partial_megafolds():
            if y == target:
                g.add(x); g.add(y)
                found = y
    assert found is not None
    d = found

    t = g.add(s.unfold(1,0,defs=d))  # problematic unfold
    for x in s.unfolds(d):
        g.add(x)

    m = make_measure(s)
    assert len(set(g)) == 7

    print(g)

    print(colors.light.green % colors.rightarrow, m(s))
    print(m(d))
    print(m(t))
    assert not m(t).is_safe()

    print(colors.light.yellow % 'unfolds:')
    A = compare(s, set(s.unfolds(d)), m=m.safe)
    print(A)
    assert len(A.xs) == 2
    assert A.accuracy == 1

    print(colors.light.yellow % 'graph:')
    A = compare(s, set(g), m=m.safe)
    print(A)
    assert len(A.xs) == 7
    assert A.precision == 1
    assert A.recall >= 5/6
    assert A.accuracy >= 6/7


def test_pqr1():

    init = Program("""
    p += 1.
    q += 1.
    r += 1.
    """)

    g = init.to_collection().partial_megafolds(init)#.partial_megafolds(init).dedup()
    print(g)

    assert len(g) == 7

    m = make_measure(init)
    a = compare(init, set(g), m=m.safe)
    print(a)
    assert a.precision == 1
    assert len(g.filter(m.safe)) > 1


def test_pqr2():

    init = Program("""
    p += 1.
    q += r.
    r += 1.
    """)

    g = init.to_collection().partial_megafolds(init).unfolds().partial_megafolds(init).dedup()
    print(g)

    assert len(g) == 14

    m = make_measure(init)
    a = compare(init, set(g), m=m.safe)
    print(a)
#    assert len(a.xs) >= 7
    assert a.precision == 1
    assert len(g.filter(m.safe)) > 1


def test_pqr3():

    init = Program("""
    p += 1.
    q += 1.
    r += 1.
    """)

    g = (
        init.to_collection()
        .partial_megafolds(init, skip_trivial=False)
        .partial_megafolds(init, skip_trivial=False)
        .dedup()
    )
    print(g)

    assert len(g) == 37, len(g)

    m = make_measure(init)
    a = compare(init, set(g), m=m.safe)
    print(a)
    assert a.precision == 1
    assert len(g.filter(m.safe)) > 1


def test_disjunctive():

    p = Program("""

    p += a * q.
    p += b * q.

    r += a.
    r += b.

    """)

    m = make_measure(p)

    assert len(p.partial_megafolds()) == 1
    assert len(p.partial_megafolds().filter(m.safe)) > 0

    p.partial_megafolds()[0].assert_equal("""
    p += r * q.
    r += a.
    r += b.
    """)


    p = Program("""

    p += a * q.
    p += b * q.

    r += c.

    c += a.
    c += tmp.

    tmp += b.

    """)

    m = make_measure(p)

    p1 = p.unfold(2,0).unfold(3,0)
    print(m(p1))

    print()
    x = p1.partial_megafolds()[0]

    print(m(x))
    pp = Program("""
    p += c * q.
    c += a.
    tmp += b.
    r += a.
    r += tmp.
    c += b.
    """)

    x.assert_equal(pp)


def test_sp():

    p = Program("""
    goal += s * p * e.
    p += 1.
    p += p * w.
    sp += s * p.

    inputs: s; w; e.
    outputs: goal.

    """)

    m = make_measure(p)
    print(m(p))

    g = p.to_collection().partial_megafolds(p).unfolds().partial_megafolds(p).dedup()
    a = compare(p, set(g), m=m.safe, D='s += 7. e += 3. w += 0.5.')
    print(a)
    assert len(g) == 11
    assert a.precision == 1
    assert len(g.filter(m.safe)) > 1


def test_slash():

    p = Program("""
    goal += a * b.
    a += 2.
    b += 3.

    goal += 5.

    outputs: goal.
    """)

    m = make_measure(p)
    print(m(p))
    w = list(map(sympy.Symbol, 'abcd'))
    mm = m(p)
    mm.m[0] = Interval(w[0],w[0])
    mm.m[1] = Interval(w[1],w[1])
    mm.m[2] = Interval(w[2],w[2])
    mm.m[3] = Interval(w[3],w[3])

    [a,b,c,d] = mm.m

    P = p.derivations(None, 'goal')

    q = p.slash('X', {0: 0, 1: 0, 2: 0, 3: 0})
    Q = q.derivations(None, 'goal')

    # these derivations happen to enumerate in the same order, but it's not
    # guarnateed to happen in generate.  That is way we have the derivation
    # mapping function (bijection)
    mP = [m(p).derivation_measure(d) for d in P]
    mQ = [m(q).derivation_measure(d) for d in Q]

    want = [a + b + c,  d]
    assert mP == want
    assert mQ == want

    assert len(P) == len(Q)
    #print(colors.yellow % 'Derivation mapping (forward):')
    for dp in P:
        dq = q.transform(dp)
        #print()
        #print(dp)
        #print(dq)
        #print(m(p).derivation_measure(dp))
        #print(m(q).derivation_measure(dq))

        assert dq.head == dp.head
        assert dq in Q

        # measures are exactly equal (no approximation error)
        assert (m(q).derivation_measure(dq)
                == m(p).derivation_measure(dp))


def test_lct():

    p = Program("""
    goal += a * b.
    a += 2.
    b += 3.

    goal += 5.

    outputs: goal.
    """)

    m = make_measure(p)
    print(m(p))
    w = list(map(sympy.Symbol, 'abcd'))
    mm = m(p)
    mm.m[0] = Interval(w[0],w[0])
    mm.m[1] = Interval(w[1],w[1])
    mm.m[2] = Interval(w[2],w[2])
    mm.m[3] = Interval(w[3],w[3])

    [a,b,c,d] = mm.m

    P = p.derivations(None, 'goal')

    q = p.lct({0: 0, 1: 0, 2: 0, 3: 0})
    Q = q.derivations(None, 'goal')

    # these derivations happen to enumerate in the same order, but it's not
    # guarnateed to happen in generate.  That is way we have the derivation
    # mapping function (bijection)
    mP = [m(p).derivation_measure(d) for d in P]
    mQ = [m(q).derivation_measure(d) for d in Q]

    want = [a + b + c,  d]
    assert mP == want
    assert mQ == want


def test_sp_mapping():
    p = Program("""
    goal += p.
    p += 1.
    p += p * 0.5.

    outputs: goal.
    """)

    m = make_measure(p)
    mm = m(p)
    mm.m = [Interval(1,1) for _ in range(len(p))]

    g = p.unfolds().megafolds(p).megafolds(p)
    q = g.min(lambda x: x.prune().degrees())
    #print(q.prune())

    q.prune().assert_equal("""
    goal += 1.
    goal += goal * 0.5.
    """)

    P = p.derivations(5, 'goal')
    Q = q.derivations(5, 'goal')

    for dp in P:
        dq = q.transform(dp)
        print()
        print(dp)
        print(dq)
        assert dp.value() == dq.value()
        assert dq in Q
        assert dp.head == dq.head

        # measure is preserved exactly in this case (no approximation error)
        mdp = m(p).derivation_measure(dp)
        mdq = m(q).derivation_measure(dq)

        assert mdp == mdq



def test_sp_mapping():
    p = Program("""
    goal += 3 * q.
    goal += 4 * q.

    p += 3.
    p += 4.

    q += 5.
    q += 7.

    outputs: goal.
    """)

    m = make_measure(p)
    mm = m(p)
    mm.m = [Interval(1,1) for i in range(1, 1+len(p))]

    g = p.megafolds(p)
    q = g.min(lambda x: x.prune().degrees())
    #print(q.prune())

    q.prune().assert_equal("""
    goal += p * q.

    p += 3.
    p += 4.

    q += 5.
    q += 7.

    """)

    P = p.derivations(None, 'goal')
    Q = q.derivations(None, 'goal')

    print(m(p))
    print(m(q))

    assert len(P) == len(Q) == 4

    for dp in P:
        dq = q.transform(dp)
        print()
        print(dp)
        print(dq)
        assert dp.value() == dq.value()
        assert dq in Q
        assert dp.head == dq.head

        # measure is preserved exactly in this case (no approximation error)
        mdp = m(p).derivation_measure(dp)
        mdq = m(q).derivation_measure(dq)

        assert mdq.lo <= mdp.lo <= mdp.hi <= mdq.hi


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
