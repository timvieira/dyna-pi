from arsenal import colors

from dyna import Program
from dyna.analyze.rewrites import Rewrites


class CoverTester:

    def __init__(self):
        self.failed = []

    def __call__(self, r, s, want, rewrites=''):
        """
        We have =, <, >, ^ (possible overlap), <> (disjoint)
        """
        if isinstance(rewrites, str): rewrites = Rewrites(rewrites)
        if isinstance(r, str): [r] = Program(r)
        if isinstance(s, str): [s] = Program(s)
        print(colors.magenta % colors.line(80))
        print(r)
        print(s)
        print('want:', want)

        supset = rewrites.covers(r, s)
        subset = rewrites.covers(s, r)   # pylint: disable=W1114

#        cap = rewrites.intersect(r, s)
#        print('RS:', cap)

        disjoint = rewrites.disjoint(r, s)
#        t = fresh(rewrites.gen(r,s))
#        print('gen:', rewrites.gen(r,s))

#        print('r', rewrites.covers(t, r) )
#        print('s', rewrites.covers(t, s) )
#        print('b', rewrites.covers(t, b) )

        if supset and subset:
            have = '='
            assert rewrites.same(r, s)
        elif supset and not subset:
            have = '>'
        elif not supset and subset:
            have = '<'
        elif disjoint:
            have = '<>'
        else:
            have = '^'

        print(f'have: {have} [{subset=}, {supset=}, {disjoint=}]')

        if have == want:
            print(colors.ok)
        else:
            print(colors.light.red % 'FAIL')
            self.failed.append((r,s,want,rewrites))
            if STOP_ON_ERROR: raise AssertionError()

    def overlaps(self, x, y, I=True, rewrites=Rewrites('')):
        if isinstance(x, str): [x] = Program(x)
        if isinstance(y, str): [y] = Program(y)
        print()
        print(x)
        print(y)
        xy = rewrites.intersect(x, y)
        print('==>', xy)
        if (xy is not None) == I:
            print(colors.ok)
        else:
            print(colors.fail)
            self.failed.append((x,y,I,rewrites))
            if STOP_ON_ERROR: raise AssertionError()


# XXX: EXPERIMENTAL
def test_anti_unifier():

    rewrites = Rewrites("""
    ks([]).
    k(K)  :- ks([K|Ks]).
    ks(Ks) :- ks([K|Ks]).

%    $fail :- k(0).
    k(s).

    """)

    def test(r, s, want):
        if isinstance(r, str): [r] = Program(r)
        if isinstance(s, str): [s] = Program(s)
        if isinstance(want, str): [want] = Program(want)
        print(colors.magenta % colors.line(80))
        print(r)
        print(s)

        have = rewrites.anti_unifier(r, s)

        print('have:', have)
        print('want:', want)
        assert want.same(want)


    test(
        "p([X|Xs]) :- k(X), ks(Xs).",
        "p([Y1,Y2|Ys]) :- k(Y1), k(Y2), ks(Ys).",
        "p([Z|Zs]) :- k(Z), ks(Zs).",
    )

    test(
        "p([X|Xs]) :- k(X), ks(Xs).",
        "p([0|Ys]) :- ks(Ys).",
        "p([Z|Zs]) :- ks(Zs).",
    )

    test(
        "p([X1,X2|Ys]) :- k(X1), k(X2), ks(Xs).",
        "p([Y1,Y2,Y3|Ys]) :- k(Y1), k(Y2), k(Y3), ks(Ys).",
        "p([Z1,Z2|Zs]) :- k(Z1), k(Z2), ks(Zs).",
    )

    test(
        "p([X1|Ys]) :- k(X), ks(Xs).",
        "p([Y1,Y2,Y3|Ys]) :- k(Y1), k(Y2), k(Y3), ks(Ys).",
        "p([Z1|Zs]) :- k(Z), ks(Zs).",
    )

    test(
        "p(Ys) :- ks(Xs).",
        "p([Y1,Y2,Y3|Ys]) :- k(Y1), k(Y2), k(Y3), ks(Ys).",
        "p(Zs) :- ks(Zs).",
    )


def test_basic_covers():

    test = CoverTester()

    test('phrase(s, Ys, I, K) += 1 is 1+1.',   # subgoal fails
         'phrase(s, Ys, I, I) += ks(Ys).',
         '<')

    test('phrase(s, Ys, I, K) += ks(Ys).',
         'phrase(s, Ys, I, I) += ks(Ys).',
         '>')

    test('phrase(s, Ys, I, K).',
         'phrase(s, Ys, I, I).',
         '>')

    test('phrase(s, Ys, I, K) += k(I) * k(K).',
         'phrase(s, Ys, I, I) += k(I).',
         '>')

    # Note: Below, k and w might overlap because we haven't given a rewrite
    # rules in this example.
    test('rewrite(X) += k(X).',
         'rewrite(X) += w(X).',
         '^')

    test('rewrite(X, Y) += k(Y) * k(X).',
         'rewrite(X, Y) += w(Y) * k(X).',
         '^')

    test('phrase(s, Ys, 0, 0) += ks(Ys).',
         'phrase(s, Ys, 0, 0) += ks(Ys).',
         '=')

    # [2021-10-18 Mon] Prior to today, the following mistake was being made.
    # The CoversRule method will continue to make it.
    #  {phrase(s, Ys, 0, 0) | ks(Ys)} >= {phrase(s, Ys, 0, 0) | ks([s | Ys])}
    #
    # Below, is a counterexample.
    # p = Program("""
    # a(Ys) += ks(Ys).
    # b(Ys) += ks([s | Ys]).
    # """)
    #
    # print(p("""
    # ks([s,b]).
    # """))
    #
    # a([s, b]).
    # b([b]).

    test('phrase(X, Ys, I, K) += ks(Ys).',
         'phrase(s, Ys, 0, 0) += ks(Ys).',
         '>')

    # this example is more difficult as it requires either "dropping" constraints
    # in the more general rule (because they are true of the bindings that get passed
    # in when the head of the rules are unified.
    test('phrase(X, Ys, J, K) += k(X) * n(J) * n(K) * ks(Ys).',
         'phrase(s, Ys, 0, 0) += ks(Ys).',
         '>',
         Rewrites("""
         n(0).  $fail :- k(0).
         k(s).  $fail :- n(s).
         """))

    test('phrase(X, Ys, I, K) += k(X) * ks(Ys) * n(I) * n(K).',
         'phrase(X, Ys, I, I) += k(X) * ks(Ys) * n(I).',
         '>')

    test('f(X) += a(X) * b(X) * c(X).',
         'f(X) += b(X) * c(X).',
         '=', Rewrites("""
         a(X) :- b(X).
         """))

    test('f(X) += a(X).',
         'f(X) += b(X).',
         '>', Rewrites("""
         a(X) :- b(X).
         """))

    test('f(X) += b(X).',
         'f(X) += a(X).',
         '>', Rewrites("""
         b(X) :- a(X).
         """))

    test('pda([X | Rest], K).',
         'pda([X, $X1 | Rest], K).',
         '>')

    # This is just an ablation of the next example which failed.
    test('pda([X | Rest], K) :- k(X), n(K).',
         'pda([X, $X1 | Rest], K) :- k(X), n(K).',
         '>')

    # Examples that use built-in evaluation and propagation
    test('f(X,2,4) += 4 is X+2.',
         'f(2,2,Z) += Z is 2+2.',
         '=')

    # disjoint because `5 is 2+2` rewrites to fail.
    test('f(X,Y,Z) += Z is X+Y.',
         'f(2,2,5).',
         '<>')

    test('f(X,Y,Z) += Z is X+Y.',
         'f(2,2,4).',
         '>')

    test('f(X,Y,Z) += Z is X+Y.',
         'f(2,2,Z).',
         '^')

    # In the example below, the pending constraints (X < Y) and (Y > X) could
    # overlap - we don't have a rewrite rule that says otherwise!
    test('f(X,Y) += X < Y.',
         'f(X,Y) += Y > X.',
         '^')

    # Our subset test is pretty brittle; in this case, we don't have enough
    # rewrites to transform in both directions; so we only succeed to get one
    # direction.  Below, we add the necessary rule.
    test('f(X,Y) += X < Y.',
         'f(X,Y) += Y > X.',
         '>', rewrites="""
         (Y<X) :- (X>Y).
         """)

    test('f(X,Y) += X < Y.',
         'f(X,Y) += Y > X.',
         '=', rewrites="""
         (Y<X) :- (X>Y).
         (Y>X) :- (X<Y).
         """)

    # I think these are equal sets if we have k(s).
    test('phrase(s, Ys, 0, 0) += ks(Ys).',
         'phrase(s, Ys, 0, 0) += ks([s | Ys]).',
         '=')

    print()
    assert not test.failed, f'{len(test.failed)} error(s), see above'


def test_free_bound():

    # XXX: When reasoning about intersection and coverage of free and bound,
    # they are disjoint.  However, when we are thinking about SIPS,
    # free(X),bound(X)==>bound(X).

    test = CoverTester()
    overlaps = test.overlaps

    test('f(X) :- $free(X).',
         'f(Y) :- $free(Y).',
         '=')

    test('f(X) += $free(X).',
         'f(Y) += $bound(Y).',
         '<>')

    test('f(Y) += $bound(Y).',
         'f(3).',
         '>')

    test('f(X,Y) += $free(X), $free(Y).',
         'f(X,Y) += $bound(X), $bound(Y).',
         '<>')

    test('f(X,Y) += $free(X), $bound(Y).',
         'f(X,Y) += $bound(X), $free(Y).',
         '<>')

    test('f(3,Y) += $free(Y).',
         'f(X,4) += $free(X).',
         '<>')

    test('f(X,Y) += $free(X), $free(Y).',
         'f(X,4) += $free(X).',
         '<>')

    test('f(X,Y) += $free(X), $free(Y).',
         'f(X,4) += $free(X).',
         '<>')

    test('f(X,Y) += $free(X), $free(Y).',
         'f(3,Y) += $free(Y).',
         '<>')

    test('f(X) :- $free(X).',
         'f(3).',
         '<>')

    overlaps('f(X,Y) :- $bound(X), $bound(Y).',
             'f(1,Y) :- $bound(Y).')

    overlaps('f(1,Y) :- $free(Y).',
             'f(1,Y) :- $bound(Y).', False)

    overlaps('f(1,X) :- $bound(X).',
             'f(X,Y) :- $bound(X), $bound(Y).')

    overlaps('f(1,Y) :- $bound(Y).',
             'f(X,2) :- $bound(X).')

    overlaps('f(1).',
             'f(Y) :- $bound(Y).')

    overlaps('f(1, Y) :-            $free(Y).',
             'f(X, Y) :- $bound(X), $bound(Y).', False)

    overlaps('f(1, Y) += $free(Y).',
             'f(1, Y) += $bound(Y).', False)

    overlaps('f(Y).',                # any != free
             'f(Y) :- $bound(Y).')

    overlaps('f(Y).',                # any != free
             'f(Y) :- $free(Y).')

    overlaps('f(Y).',
             'f(1).')

    overlaps('f(g(X), X) :- $bound(X).',
             'f(g(X), 3) :- $bound(X).')

    overlaps('f(g(X), X) :- $free(X).',
             'f(g(X), X) :- $bound(X).', False)

    #_______
    # SDD

    overlaps('f(A,A,B) :- $free(A), $free(B).',
             "f(A',B',B') :- $free(A'), $free(B').", False)

    overlaps('f(A,A,B) :- $free(A), $free(B).',
             'f(C,C,C) :- $free(C).', False)

    overlaps('f(A,B,C) :- $free(A), $free(B), $free(C).',
             'f(C,C,C) :- $free(C).', False)

    assert not test.failed, f'got {len(test.failed)} error(s), see above'


def test_advanced_covers():

    test = CoverTester()

    ks_theory = Rewrites("""
    ks([]).
    k(K)  :- ks([K|Ks]).
    ks(Ks) :- ks([K|Ks]).

    %ks([K|Ks]) :- k(K), ks(Ks).

    """)

    test('p(Xs)     += ks(Xs).',
         'p([Y|Ys]) += k(Y), ks(Ys).',
         '>',
         ks_theory)

#    assert not test.failed, f'{len(test.failed)} error(s), see above'
#    return

    test('p([X|Xs])     += k(X) * ks(Xs).',
         'p([Y1,Y2|Ys]) += k(Y1) * k(Y2) * ks(Ys).',
         '>',
         ks_theory)


    test('p(Xs)  += ks(Xs).',
         'p([X]) += k(X).',
         '>',
         ks_theory)

    test('p(Xs)      += ks(Xs).',
         'p([X1,X1]) += k(X1), k(X2).',
         '>',
         ks_theory)


    assert not test.failed, f'{len(test.failed)} error(s), see above'
    return

    # TODO: The examples below fail because we don't really handle the local
    # variables.
    #
    # TODO: also this example
    # f(X) :- g(X,Y).
    # f(X) :- g(X,Z).   % Y and Z are local variables

    test("beta(S) += n(S).",
         "beta(S) += n(S), n(S').",
         '>')

    test("beta(S) += n(S), n(S').",
         """beta(S") += n(S), n(S'), n(S").""",
         '>')

    # TODO: support rewrites for structural equality constraints
    if 0:
        r,s = Program("""
        Y :- (Y=f(X)).
        f(X).
        """)
        test(r, s, '=', Rewrites("""
        """))



#from dyna import Subst, Rule
#from dyna.propagate import scons
#
#def simple_union(rewrites, r, s):
#
#    subst = Subst().mgu(r.head, s.head)
#    if subst is Subst.FAIL: return
#
#    # substitution constraints
#    sc = scons(subst)
#
#    # specialize the r rule to match s's head.
#    S = rewrites(Rule(s.head, *s.body, *sc), drop_checked=False)
#    R = rewrites(Rule(r.head, *r.body, *sc), drop_checked=False)
#
#    print('R=',R)
#    print('S=',S)
#
#    return Rule(S.head, *set(S.body).intersection(set(R.body)), *sc)
#
#
#def test_anti_unifier():
#
#    [r,s] = Program("""
#
#    f(X) += g(X) * h(X).
#    f(X) += g(X).
#
#    """).normalize_unification2()
#
#    theory = Rewrites()
#
#    t = simple_union(theory, r, s)
#    print(t)
#    t.to_program().compare('f(X) += g(X).')
#
#
#    [r,s] = Program("""
#
#    f(3,Y).
#    f(X,4).
#
#    """).normalize_unification2()
#    print(r)
#    print(s)
#    t = simple_union(theory, r, s)
#    print(t)
#    t.to_program().compare('f(X,Y).')


def main():
    global DEBUG, STOP_ON_ERROR
    from arsenal.testing_framework import TestingFramework
    F = TestingFramework(globals())
    F.cli.add_argument('--debug', type=int, default=0)
    F.cli.add_argument('--stop-on-error', action='store_true')
    args = F.cli.parse_args()
    DEBUG = args.debug
    STOP_ON_ERROR = args.stop_on_error
    F.run()


if __name__ == '__main__':
    main()
