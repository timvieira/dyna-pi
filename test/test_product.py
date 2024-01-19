# TODO: rename this module to test_product.py
from arsenal import colors, ok
from collections import Counter

from dyna.term import vars, Var, Term, unify, Subst, FAIL, Product, flatten, flatten_op, fresh
from dyna.syntax import term
from dyna.pretty import PrettyPrinter


# TODO: support unifications and other theories:
#  f(X,Y), X=Y` <==> f(X,X) <==> f(Y,Y)

# TODO: memoize!

# TODO: use subgoal bucketing (by some appropriate term signature) to speed-up
# bigger matchings.


def check_covering(xs, ys, subst, alignment, verbose=False):
    assert len(alignment) == len(xs)
    for j,i in alignment.items():
        if verbose: print(' ', subst(xs[i]), '==', ys[j])
        assert subst(xs[i]) == ys[j]


def test_match_comm():

    def test_case(a, b, want):

        pp = PrettyPrinter()
        [_, a, b] = term(f'$covers(({a}), ({b}))', freshen=True)
#        b = fresh(b)
        # Warning: assumes ,/2 not */2.
        a, b = (Product(flatten_op(a, '*')), Product(flatten_op(b, '*')))
        #assert want in {'<', '>', '=', '<>'}
        #print('test', a, colors.green % want, b)
        print(colors.yellow % 'test', pp(a), colors.yellow % 'vs', pp(b))
        assert vars(a).isdisjoint(vars(b))

        solutions = set()
        for s in a.match_comm(b):
            print(f'  → {s.is_non_specializing()}: {pp(s)}')
            if s.is_non_specializing():
                solutions.add(frozenset(s.items()))

        assert len(solutions) == want, [len(solutions), want]

    test_case('f(X)', 'f(Y)', 1)
    test_case('g(Y) * f(Y)', 'f(X) * g(X)', 1)
    test_case('f(X)', 'f(Y) * g(Y)', 0)
    test_case('f(X) * g(Y)', 'f(Z) * g(Z)', 0)
    test_case('f(X) * f(Y)', 'f(W) * f(Z)', 2)
    test_case('f(X) * f(Y) * f(Z)', 'f(A) * f(B) * f(C)', 6)
    test_case('f(X) * f(Y) * f(Z)', 'f(1) * f(B) * f(C)', 0)
    test_case('f(X) * f(Y) * f(1)', 'f(1) * f(B) * f(C)', 2)


def test_covers_product():

    def test_case(a, b, want):
        [_, a, b] = term(f'$covers(({a}), ({b}))', freshen=True)
        # Warning: assumes ,/2 not */2.
        a, b = (Product(flatten(a)), Product(flatten(b)))
        assert want in {'<', '>', '=', '<>'}
        print('test', a, colors.green % want, b, end=' ')

        ab = list(a.covers(b))
        ba = list(b.covers(a))

        for subst, align, _ in ab:
            check_covering(a, b, subst, align)

        for subst, align, _ in ba:
            check_covering(b, a, subst, align)

        if ab and ba:
            have = '='
        elif ab and not ba:
            have = '>'
        elif not ab and ba:
            have = '<'
        else:
            have = '<>'

        assert have == want, f'have: "{have}", want: "{want}"'

        print(ok)

#    global USE_HEURISTIC
#    from arsenal import timers
#    T = timers()
#
#    def test_case(*args):
#        USE_HEURISTIC = True
#        with T[USE_HEURISTIC]:
#            _test_case(*args)
#
#        USE_HEURISTIC = False
#        with T[USE_HEURISTIC]:
#            _test_case(*args)

    # Recover ordinary behavior
    test_case('f(X)', 'f(X)', '=')
    test_case('f(X)', 'f(Y)', '=')
    test_case('f(X)', 'g(X)', '<>')
    test_case('Y', 'f(X)', '>')
    test_case('X', 'Y', '=')

    test_case('f(X)', 'f(X), g(X)', '>')
    test_case('f(X)', 'f(Y), g(Y)', '>')
    test_case('f(X)', 'f(Y), g(Z)', '>')

    test_case('f(1)', 'f(2)', '<>')
    test_case('f(X)', 'f(2),f(Y)', '>')
    test_case('f(X,Y)', 'f(Z,Z)', '>')
    test_case('f(X,Y), f(Y,X)', 'f(I,J), f(J,I)', '=')

#    test_case('f(X,Y), f(Y,X)', 'f(I,I), f(J,J)', '>')

    test_case('a(I), b(I, J)', 'b(I", 4), a(I")', '>')
    test_case('a(I), b(I, J)', 'b(I", 4), a(I"), d(J")', '>')

    # It's a strange comparison to make because
    #  the set of the right is a set of triples
    #  and the set of the left is a set of pairs
    # There is a subset relationship because the triples <I,J,K>
    # can be filtered so that I=K gives the tuples on the left.
    test_case('f(X,Y), f(Y,X)', 'f(I,J), f(J,K)', '<')

    # * permuting order on left doesn't help
    test_case('f(X)', 'g(X), f(X)', '>')
    test_case('a(X), b(X), c(X), d(X)', 'd(X), c(X), b(X), a(X), h(X)', '>')
    test_case('a(X), b(Y), c(X), d(Z)', 'd(X), c(X), b(X), a(X), h(X)', '>')
    test_case('a(X), b(X), c(X), d(X)', 'd(X), c(X), b(X), a(X), h(X)', '>')

    test_case('f(X)', 'f(Y), g(Y)', '>')

    test_case('f(X), G', 'f(Y), g(Y)', '>')

    test_case('g(Y), f(X,Y)', 'f(X,Y), g(Y)', '=')

    test_case('g(X,Y), f(Y,Z)', 'f(B,C), g(A,B)', '=')
    test_case('Z', 'g(Y), f(X,Y)', '>')

    # The following are only equal under idempotence...
    test_case('X', 'W, Y, Z', '>')
    test_case('W', 'X, Z', '>')
    test_case('f(X)', 'f(X), f(X)', '>')
    test_case('f(X)', 'f(Y), f(Y)', '>')

    test_case("phrase(Z', J', K'), rewrite(X', Y', Z')",
              "phrase(Z, J, K), rewrite(X, Y, Z)", '=')

    test_case("phrase(Z', J', K'), rewrite(X', Y', Z')",
              "phrase(Y, I, J), phrase(Z, J, K), rewrite(X, Y, Z)", '>')

    test_case('f(X1,X2), f(X2,X3), f(X3,X1)',
              'f(Y1,Y2), f(Y3,Y1), f(Y2,Y3)', '=')

    # Lists of length >= 2 ⊇ lists of length >= 3.
    test_case('pda([A, B | Rest], I, K)', "pda([X1, X2, X3 | X2], I', K')", '>')

#    T.compare()


if __name__ == '__main__':
    from arsenal.testing_framework import testing_framework
    testing_framework(globals())
