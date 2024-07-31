from arsenal import colors

from dyna import Program, vars, pp
from dyna.analyze.runtime import type_bound, Simplify, Symbol
from arsenal.maths.combinatorics import powerset


# TODO: these "tests" are missing assertions
def test_cky_less():

    p = Program("""
    phrase(X,I,K) += rewrite(X,Y,Z) * phrase(Y,I,J) * phrase(Z,J,K).
    phrase(X,I,K) += rewrite(X,Y) * phrase(Y,I,K).
    phrase(X,I,K) += rewrite(X,Y) * word(Y,I,K).
    goal += phrase("ROOT", 0, N) * length(N).
    """)

    S = p.type_analysis("""

    word(X,I,K) :- w(X), n(I), n(K), (I < K).
    rewrite(X,Y,Z) :- k(X), k(Y), k(Z).
    rewrite(X,Y) :- k(X), k(Y).
    rewrite(X,Y) :- k(X), w(Y).
    length(I) :- n(I).

    inputs: k(_); n(_); w(_); (_ < _).

    """, """

    k("ROOT").
    $fail :- k(X), w(X).
    n(0).
    (I < K) :- (I < J), (J < K).
    $fail :- (I < J), (J < I).
    $fail :- (I < I).
    """)

    S.assert_equal("""
    word(X, I, K) += n(I) * (I < K) * n(K) * w(X).
    rewrite(X, Y, Z) += k(Y) * k(X) * k(Z).
    rewrite(X, Y) += k(X) * k(Y).
    rewrite(X, Y) += w(Y) * k(X).
    length(I) += n(I).
    phrase(X, I, K) += (I < K) * k(X) * n(K) * n(I).
    goal.
    """)

    qs = Program('rewrite(X,Y). phrase(X,I,K).')

    for q in qs:
        print()
        print(colors.yellow % pp(q, color=False))
        for V in powerset(vars(q)):
            print(type_bound(S, q, V = set(V)),
                  colors.magenta % 'mode:', set(V) or {})

    S.show_runtime()


def test_builtins():

    p = Program("""
    f(X,Y) += (X < Y) * n(X) * n(Y).

    g(X,Y) += (X < Y).

    inputs: n(_).
    """)

    S = p.type_analysis('n(X) += k(X). inputs: k(_); (_ < _).')

    S.assert_equal("""
    n(X) += k(X).
    f(X,Y) += k(X) * k(Y) * (X < Y).
    g(X,Y) += (X < Y).
    """)

    qs = Program('f(X,Y). g(X,Y).')

    print(colors.yellow % 'size bounds:')
    for q in qs:
        print(colors.yellow % pp(q, color=False))
        for V in powerset(vars(q)):
            b = type_bound(S, q, V = set(V))
            print(Simplify(b),
                  colors.magenta % 'mode:', set(V) or {})

    print()
    print(colors.yellow % 'runtime bounds:')
    S.show_runtime()


def test_join():

    p = Program("""
    a(I,K) += b(I,J) * c(J,K).

    inputs: b(_,_): c(_,_).
    """)

    S = p.type_analysis("""
    b(I,J) += b₁(I) * b₂(J).
    c(J,K) += c₁(J) * c₂(K).

    inputs: b₁(_); c₁(_); b₂(_); c₂(_).
    """)
    print(S)

    qs = Program('a(I,K).')

    print(colors.yellow % 'size bounds:')
    for q in qs:
        print(colors.yellow % pp(q, color=False))
        for V in powerset(vars(q)):
            b = type_bound(S, q, V = set(V))
            print(Simplify(b),
                  colors.magenta % 'mode:', set(V) or {})

    S.show_size(full=True)

    import sympy
    b1, b2, c1, c2 = map(Symbol, ['b₁','b₂', 'c₁', 'c₂'])
    assert sympy.simplify(S.size().x) == b1*b2 + c1*c2 + b1*c2

    [q] = Program('a(I,K).'); I,K = q.head.args
    bound = type_bound(S, q, V = {I,K})
    assert bound.x == 1

    bound = type_bound(S, q, V = {I})
    assert bound.x == c2

    bound = type_bound(S, q, V = {K})
    assert bound.x == b1

    bound = type_bound(S, q, V = set())
    assert bound.x == b1 * c2


    print()
    print(colors.yellow % 'runtime bounds:')
    S.runtime()

    assert sympy.simplify(S.runtime().x) == sympy.simplify(sympy.Min(b1*b2*c2 + b1*b2, b1*c1*c2 + c1*c2) + 3)


def test_infinite():

    p = Program("""
    a(I) += 1.
    """)

    t = p.type_analysis()
    print(t)

    t.show_size()

    assert t.size().x == float('inf')


if __name__ == '__main__':
    from arsenal.testing_framework import TestingFramework
    F = TestingFramework(globals())
    F.cli.add_argument('--debug', type=int, default=0)

    import dyna.analyze.runtime
    dyna.analyze.runtime.DEBUG = max(dyna.analyze.runtime.DEBUG,
                                     F.cli.parse_args().debug)
    F.run()
