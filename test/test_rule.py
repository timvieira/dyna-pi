from arsenal import colors
from dyna import Program


def test_folds_by():

    [r,s] = Program("""

    goal += a * b(X1) * c(Y) * b(X2).
    bc(X,Y) += b(X) * c(Y).

    """)

    print(r.folds_by(s))
    [r1,r2] = r.folds_by(s)
    print(r1)
    print(r2)

    assert r1.same(r2)

    [r,s] = p = Program("""
    goal += b(X) * c(X) * d(Z).
    foo(X,Y) += b(X) * c(X).   % Y is free
    """)

    # Currently, the fold below fails - it's because we snag the extra Y variable.
    Program(list(r.folds_by(s))).assert_equal("""
    goal += foo(X,"junk") * d(Z).
    """)

    # Proof of concept: We can allow this fold by simply binding Y to something
    # arbitrary.  Here are three arbitrary choices:
    Program("""
    goal += foo(X,X) * d(Z).
    foo(X,Y) += b(X) * c(X).
    """).unfold(0,0).assert_equal(p)
    Program("""
    goal += foo(X,Z) * d(Z).
    foo(X,Y) += b(X) * c(X).
    """).unfold(0,0).assert_equal(p)
    Program("""
    goal += foo(X,"junk") * d(Z).
    foo(X,Y) += b(X) * c(X).
    """).unfold(0,0).assert_equal(p)


    # [2022-03-04 Fri] below is an the test case that brought to helped me
    # figure out the "junk binding trick".  Without the trick we find the fold
    # proposal:
    #
    #  goal(I) += goal(I) / x(I) * x(I').
    #
    # instead of the fold you'd expect, which is
    #
    #  goal(I) += goal(I) / x(I') * x(I').
    #
    # This is because the variables in head aren't connected to the body in the
    # folder `goal(I') / x(I')) += g(J)`.  Since this variable is just dangling,
    # we get an unwanted infinite multiplicity contribution.  The fix is to bind
    # it to something arbitrary.
    #
    p0 = Program("""
    goal(I) += x(I) * g(J).
    (goal(I') / x(I')) += g(J).
    """)

    # Proof of concept: unfolding works (note unfold introduces I=I')
    Program("""
    goal(I) += goal(I) / x(I') * x(I').
    (goal(I') / x(I')) += g(J).
    """).unfold(0,0).assert_equal("""
    goal(I) += x(I) * g(J).
    (goal(I') / x(I')) += g(J).
    """)

    [r,s] = p0
    Program(list(r.folds_by(s))).assert_equal("""
    goal(I) += goal("junk") / x("junk") * x(I).
    """)


def test_can_elim():

    def analyze(x):
        [r] = Program(x)
        return r.analyzer

    a = analyze('goal(X,Y,Z) += f(X,Y,Z).')
    assert len(a.can_elim) == 0
    assert a.local_vars == set()

    a = analyze('goal(X) += f(X,Y).')
    assert len(a.can_elim) == 0, a.can_elim

    a = analyze('goal += f(X,Y,Z)*g(X,Y,Z).')
    assert len(a.can_elim) == 0, a.can_elim

    a = analyze('goal += f(X,Y,Z)*g(X,Y,Z)*h(Z).')  # can eliminate the X and Y
    assert len(a.can_elim) == 2, a.can_elim

    a = analyze('goal += f(X,Y)*g(Y,Z).')   # can elim X or Z
    assert len(a.can_elim) == 2, a.can_elim

    a = analyze('goal(X,Z) += f(X,Y)*g(Y,Z).')
    assert len(a.can_elim) == 0

    a = analyze('goal += 1.')
    assert len(a.can_elim) == 0

    a = analyze('goal(X) += 1.')
    assert len(a.can_elim) == 0

    print('ok')


def test_rule_same():

    def test_case(r, s, want):
        assert isinstance(r, str) and isinstance(s, str)
        [r, s] = Program(r + '\n' + s)

        assert want in {'<', '>', '=', '<>'}
        print('test', r, colors.green % want, s, end=' ')

#        ab = _same_rule_helper(a, b)
#        ba = _same_rule_helper(b, a)

        same = r.same(s)
        assert same == s.same(r)   # should be symmetric

        # [2022-11-07 Mon] rule "subset" no longer supported.
        if want != '=':
            want = '<>'

        if same:
            have = '='
        else:
            have = '<>'

        if have == want:
            print(colors.ok)
        else:
            print(colors.fail, f'have: "{have}", want: "{want}"')

    test_case('startpath(I,K) += edge(J,K) * startpath(I,J).',
              "startpath(III,K) += startpath(II,J) * edge(J,K).", '<')

    test_case('goal(X) += f(X,Y) * g(Y,X).',
              'goal(X) += g(Y,X) * f(X,Y).', '=')

    test_case('goal(X) += f(X,Y) * g(X,Y).',
              'goal(X) += f(X,Y) * g(X",Y").', '<>')

    test_case('goal(X) += f(X,Y) * g(X,Y).',
              'goal(1) += f(1,2) * g(1,2).', '<>')

    test_case('f(X) += goal(X) * g(X).',
              'goal(X) += g(X) * f(X).', '<>')

    test_case('f(X) += 1.',
              'goal(X) += g(X) * f(X).', '<>')

    test_case('goal(X) += f(X) * g(X).',
              'loag(X) += g(X) * f(X).', '<>')

    test_case('goal(1) += f(X) * g(X).',
              'goal(X) += g(X) * f(X).', '<>')

    # Bind an output variable - ok
    test_case('goal(3,Y,Z) += g(3,Y) * f(3).',
              'goal(X,Y,Z) += g(X,Y) * f(X).', '<')

    # Incompatible output variable bindings
    test_case('goal(3,Y) += g(3,Y) * f(3).',
              'goal(X,4) += g(X,4) * f(X).', '<>')

    # Bind a local variable - bad
    test_case('mv(X) += m(X,2) * v(2).',
              'mv(X) += v(Y) * m(X,Y).', '<')




def test_same():

    def test_case(r, s, want):
        assert isinstance(r, str) and isinstance(s, str)
        [a, b] = Program(r + '\n' + s)

        assert want in {True, False}
        print('test', a, colors.green % want, b, end=' ')

        have = a.same(b)
        if have == want:
            print(colors.ok)
        else:
            print(colors.fail, f'have: "{have}", want: "{want}"')


    test_case(
        'goal += path(J,K) * start(I) * edge(I,$J1) * path($J1,J) * stop(K).',
        'goal += path(I,J) * start(I) * path(J,$J1) * edge($J1,K) * stop(K).',
        False
    )

    test_case(
        'path(I,K) += edge(I,$J1) * path($J1,J) * path(J,K).',
        'path(I,K) += path(I,J) * path(J,$J1) * edge($J1,K).',
        False
    )

    test_case(
        'path(I,K) += path(J,K) * path(I,$J1) * edge($J1,J).',
        'path(I,K) += path(J,$J1) * path(I,J) * edge($J1,K).',
        False,
    )

    test_case('x += x * a * a.',
              'x += x * a * a.', True)

    test_case('goal(X) += f(X,Y) * g(Y,X).',
              'goal(X) += g(Y,X) * f(X,Y).', True)

    test_case('goal(X) += f(X,Y) * g(Y,X).',
              'goal(X) += g(Y,X) * f(X,X).', False)

    test_case('f(X) += goal(X) * g(X).',
              'goal(X) += g(X) * f(X).', False)

    test_case('tmp += f(X) * g(Y).',
              'tmp += f(X) * g(X).', False)

    test_case('goal(X) += f(X) * g(X).',
              'loag(X) += g(X) * f(X).', False)

    test_case('goal(1) += f(X) * g(X).',
              'goal(X) += g(X) * f(X).', False)

    # Incompatible output variable bindings
    test_case('goal(3,Y) += g(3,Y) * f(3).',
              'goal(X,4) += g(X,4) * f(X).', False)

    # Bind a local variable - bad
    test_case('mv(X) += m(X,2) * v(2).',
              'mv(X) += v(Y) * m(X,Y).', False)



if __name__ == '__main__':
    from arsenal.testing_framework import testing_framework
    testing_framework(globals())
