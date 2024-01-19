from arsenal import colors
from dyna import Program, Rule, vars, Subst, ConstraintPropagation


def test_rewrites():

    R = ConstraintPropagation(Program("""
    ks([]).
    ks(Xs) :- ks([X|Xs]).
    k(X) :- ks([X|Xs]).

    ws([]).
    ws(Xs) :- ws([X|Xs]).
    w(X) :- ws([X|Xs]).

    % < is a strict partial order
    $fail :- (I<I).         % irreflexive
    $fail :- (I<J),(J<I).   % asymmetric
    (I<K) :- (I<J),(J<K).   % transitive

    k(s).
    n(0).

    $fail :- k(X), n(X).
    $fail :- k(X), w(X).
    $fail :- w(X), n(X).

    % inherited by disjointness
    % !n(s)
    % !k(0)

    """, '(_ < _). k(_). n(_). ks(_).'))

    fails = []

    def simplify(r):
        if r is None: return
        return Rule(r.head, *[
            x for x in r.body
            if vars(x) <= vars(r.head) and vars(x)
        ])

    def error(r, want, have, R, theory):  # pragma: no cover
        if keep_going:
            fails.append((r,want,have,theory))
        else:
            print(r)
            print('HAVE:', have)
            print('WANT:', want)
            print(R.chart)
            print(R.bindings)
            raise AssertionError()


    keep_going = True
    def test(r, want, theory=R):
        if isinstance(r, str): [r] = Program(r)
        if isinstance(want, str): [want] = Program(want)
        print()
        print(colors.light.yellow % 'rule:', r)
        chart = theory(r.body)
        if chart is None:
            have = None
        else:
            have = simplify(Rule(r.head, *chart))
            have = Subst({x:y for _,x,y in theory.bindings})(have)

        #print('CLOSURE:', chart)

        print('HAVE:', have)
        print('WANT:', want)

        if have is None or want is None:
            if have == want:
                print(colors.light.green % 'ok')
            else:  # pragma: no cover
                print(colors.light.red % 'fail')
                error(r,want,have,R,theory)
            return

        if have.same(want):
            print(colors.light.green % 'ok')
        else:   # pragma: no cover
            print(colors.light.red % 'fail')
            error(r,want,have,R,theory)

    test('goal(X) += n(X).',
         'goal(X) += n(X).')

    test('goal += n(X).',
         'goal.')

    test('goal += n("mystery").',
         'goal.')

    test('goal += k("mystery").',
         'goal.')

    test('goal += n("mystery"), k("mystery").',
         None)

    test('goal += n(X), k(X).',
         None)

    test('goal += k(X), n(X).',
         None)

    test('goal += n(0).',
         'goal.')

    test('goal += n(s).',
         None)

    test('goal += k(0).',
         None)

    test('goal(X) += n(0), n(0), k(X).',
         'goal(X) += k(X).')

    test('goal += n(0), n(s), k(0).',
         None)

    test('goal(A,B,C) += (A<B), (B<A).',
         None)

    test('goal(A,B,C) += (A<A).',
         None)

    test('goal(A,B,C) += (A<B), (B<C).',
         'goal(A,B,C) += (A<B), (B<C), (A<C).')

    # will propagate
    test('goal(A,B,C,D) += (A<B), (B<C), (C<D).',
         'goal(A,B,C,D) += (A<B), (A<C), (A<D), (B<C), (B<D), (C<D).')

    # impossible less than chain
    test('goal(A,B,C,D) += (A<B), (B<C), (C<D), (D<A).',
         None)

    test('beta(s,Ys,0,K) :- ks([W|Ys]), n(0), k(W), n(K).',
         "beta(s,Ys,0,K) :- n(K), ks(Ys).")

    test('goal(Y,Ys) :- ks([Y|Ys]).',
         'goal(Y,Ys) :- ks([Y|Ys]), k(Y), ks(Ys).')

    test('goal(X,Y,Z) :- ks([X,Y,Z]).',
         'goal(X,Y,Z) :- ks([X, Y, Z]) * ks([Y, Z]) * ks([Z]) * k(X) * k(Y) * k(Z).')

    test('goal(X,Y,Z) :- ks([s,s,s]).',
         'goal(X,Y,Z).')

    test('goal(X,Y,Z) :- ks([s,0,s]).',
         None)

    test('goal(X,Y,Z) :- ks([X,Y,Z]), n(Z).',
         None)

    # TODO: we should be able to prove that these lists are disjoint
    #test('goal :- ks(Xs), ws(Xs).',
    #     None, theory=R)


    R2 = ConstraintPropagation(Program("""
    ks([]).
    ks(Xs) :- ks([X|Xs]).
    k(X) :- ks([X|Xs]).

    k(X) :- k1(X).        % subtype
    k(X) :- k2(X).        % subtype
    $fail :- k(X), n(X).  % disjoint

    n(0).
    k(s).
    k1(s1).
    k2(s2).

    $fail :- k1(X), k2(X).  % disjoint

    """, 'ks(_). k(_). k1(_). k2(_). n(_).'))

    # subtype and disjoint type of parent type are also disjoint
    test('goal(X) :- n(X), k2(X).',
         None, theory=R2)

    test('goal(X) :- k(X).',
         'goal(X) :- k(X).', theory=R2)

    test('goal(X) :- k1(X).',
         'goal(X) :- k1(X), k(X).', theory=R2)

    # subtype and disjoint type of parent type are also disjoint
    test('goal :- n(s2).',
         None, theory=R2)

    # Below, are some very basic tests for built-in evaluation
    R0 = ConstraintPropagation('')
    test('goal(X) :- (X is 3 + 1).',
         'goal(4) :- (4 is 3 + 1) * (4 = 4).', theory=R0)

    test('goal :- (11 is 3 + 1).',  # builtin-constraint fails
         None, theory=R0)

    theory = ConstraintPropagation("""
    (I < K) :- (I < J), (J < K).
    $fail :- (I < J), (J < I).
    $fail :- (I < I).
    (X < Y) :- (Y > X).  % canonicalize to less than.
    """)

    test('zoo += 18.0 * (Z is 4 + 4) * (8 is 4 + 4) * (8 < 4) * (Z < 4) * (4 > 8) * (Z = 8) * (4 > Z).',
         None, theory=theory)

    assert len(fails) == 0, f'{len(fails)} tests failed.'



if __name__ == '__main__':
    from arsenal.testing_framework import TestingFramework
    F = TestingFramework(globals())
    F.cli.add_argument('--debug', type=int, default=0)
    DEBUG = F.cli.parse_args().debug
    F.run()
