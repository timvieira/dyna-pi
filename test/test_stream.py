from dyna import Program, Rule, Product, term, flatten_op, fresh, ResultStream, I, Constant
from semirings import MaxTimes


# implementation of unfolding using the stream DSL
def test_unfold():

    p = Program("""
    path(I,J) += f(I,J).
    path(I,K) += 3 * f(I,J) * 2 * f(J,K).
    path(I,L) += f(I,J) * f(J,K) * f(K,L) * 1.

    f(1,2) += 5.
    f(2,3) += 6.
    f(3,4) += 7.
    f(3,5) += 8.

    """)

    i = 1
    j = 1
    q = p.unfold(i,j)

    # remove the rule
    r = p.rules[i]

    u = p - {i}
    u[r.head] = Constant(r.body[:j]) * p[r.body[j]] * Constant(r.body[j+1:])

    u.constant_folding().assert_equal(q.constant_folding())


def test_unfold_multiplicity_correction():
    p = Program("""
    goal += f(X).

    f(X) += 4.

    """)

    i = 0
    j = 0
    q = p.unfold(i,j)

    # remove the rule
    r = p.rules[i]

    u = p - {i}
    u[r.head] = Constant(r.body[:j]) * p[r.body[j]] * Constant(r.body[j+1:])

    u.constant_folding().assert_equal(q.constant_folding())


#def test_basics():
#
#    p = Program("""
#    path(I,J) += f(I,J).
#    path(I,K) += 3 * f(I,J) * 2 * f(J,K).
#    path(I,L) += f(I,J) * f(J,K) * f(K,L) * 1.
#
#    f(1,2) += 1.
#    f(2,3) += 1.
#    f(3,4) += 1.
#    f(3,5) += 1.
#
#    """)
#    S = ResultStream
#    q = p
#    # advanced usage: sums and proj
#    for s in S.sum([(lambda v,r=r: Rule(r.head, v)) @ S.product(q.q(y) for y in r.body)
#                    for r in p]):
#        print(s)
#    want = p.solve()
#    have = fancy_naive_fc(p)
#    have.assert_equal(want)
#    p = p.binarize()
#    want = p.solve()
#    have = fancy_agenda_fc(p)
#    have.assert_equal(want)


#def fancy_naive_fc(p):
#    old = Program()
#    while True:
#        new = Program()
#        for r in p:
#            new.r(r.head, *[old.q(y) for y in r.body])
#        if old == new: return new
#        old = new.constant_folding()


#def fancy_agenda_fc(p):
#
#    m = Program()
#    d = p.step(m)
#
#    while True:
#        d = d.constant_folding()
#        m = m.constant_folding()
#        if len(d) == 0:
#            return m
#
#        s = d.rules.pop(0)
#        w = s.head
#        [v] = s.body
#
#        if v == 0: continue
#
#        for r in p:
#
#            if len(r.body) == 1:
#                [x,y] = r
#                d.r(x, I(y,w,v))
#
#            if len(r.body) == 2:
#                [x,y,z] = r
#                d.r(x, I(y,w,v), m.q(z))
#                d.r(x, m.q(y), I(z,w,v))
#                d.r(x, I(y,w,v), I(z,w,v))
#
#        m.r(w, I(w,w,v))


def test_rule_adding():

    q = Program("""
    f(1) += 2.
    f(2) += 3.
    f(3) += 4.

    q(a(b(c(X)))) += 2.
    q(5) += 10.

    """)

    p = Program()
    p[term('a')] = Product()
    p.assert_equal('a.')

    # add the rule using `r` method without expanding it
    p = Program()
    for r in Program('g(X) += f(X) * f(X).'):   # nonlinear
        p[r.head] = r.body
    p.assert_equal('g(X) += f(X) * f(X).')

    p = Program()
    [r] = Program('h(X) += f(X) * f(X).')
    p[r.head] = q[r.body]
    p.assert_equal('h(1) += 4. h(2) += 9. h(3) += 16.')

    # infinite multiplicity test cases
    p = Program()
    [r] = Program('tmp(X) += q(X).')
    p[r.head] = q[r.body]
    p.assert_equal("""
    tmp(a(b(c(X)))) += 2.0.
    tmp(5) += 10.0.
    """)

    p = Program()
    [r] = Program('goal += q(X) * q(X).')
    p[r.head] = q[r.body]
    p.assert_equal('goal += ∞.')

    p = Program(semiring=MaxTimes)
    [r] = Program('goal += q(X) * q(X).')
    p[r.head] = q.lift_semiring(MaxTimes)[r.body]
    p.assert_equal(Program('goal += 100. goal += 2.').lift_semiring(MaxTimes))


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
