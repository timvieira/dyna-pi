from dyna import Program
from dyna.term import same, covers
from dyna import term
from dyna.analyze.types import truncate_term


def test_truncate_term():

    def test(x, z, D):
        x = term(x)
        y = truncate_term(x, D)
        z = term(z)
        print()
        print(x)
        print(y)
        print(z)
        assert same(y, z)
        assert covers(z, x)

    test('f(f(f(f(f(f(X))))))',
         'f(f(_))', 2)

    test('f(f(f(f(f(f(X))))))',
         'f(f(f(f(f(f(X))))))', 10)

    test('f(f(f(f(f(f(X))))), g(X))',
         'f(_, _)', 1)

    test('f(f(f(f(f(f(X))))), g(X))',
         'f(f(_), g(_))', 2)

    test('[1,2,3,4,5]',
         '[1,2,_|_]', 3)   # not quite what I wanted, but it seems fine.

    test('[X,X,X,X,X]',
         '[X,X,_|_]', 3)   # not quite what I wanted, but it seems fine.


def test_split_slash():
    p = Program("""
    % 0 right children so far
    rconstit(X:H,I,K) += rewrite(X,H) * word(H,I,K).

    % add right child
    rconstit(X:H,I,K) += rewrite(X:H,Y:H,Z:H2) * rconstit(Y:H,I,J) * constit(Z:H2,J,K).

    % 0 left children so far
    constit(X:H,I,K) += rconstit(X:H,I,K).

    % add left child
    constit(X:H,I,K) += rewrite(X:H,Y:H2,Z:H) * constit(Y:H2,I,J) * constit(Z:H,J,K).

    goal += constit(s:H,0,N) * length(N).

    inputs: rewrite(_,_); rewrite(X:H,Y:H2,Z:H3); word(_,_,_); length(_).
    outputs: goal.
    """)

    # annoying work around because term uses a differently configured parser
    G = Program('rconstit(X0:H0,J0,K0).').rules[0].head
    q = p.slash(G, {2: 0, 3: 2})

    S = q.type_analysis()

    S.assert_equal("""
    $other(rconstit(X: H,I,K)) += $bound(H) * $bound(I) * $bound(K) * $bound(X).
    (constit(X: H0,I,K0) / rconstit(X0: H0,J0,K0)) += $bound(X0) * $free(K0) * $bound(I) * $bound(J0) * $bound(H0) * $bound(X).
    (constit(X0: H0,J0,K0) / rconstit(X0: H0,J0,K0)) += $free(K0) * $free(H0) * $free(J0) * $free(X0).
    (rconstit(X0: H0,J0,K0) / rconstit(X0: H0,J0,K0)) += $free(H0) * $free(X0) * $free(K0) * $free(J0).
    constit(X0: H0,J0,K0) += $bound(J0) * $bound(K0) * $bound(X0) * $bound(H0).
    goal.
    length($Gen6) += $bound($Gen6).
    rconstit(X0: H0,J0,K0) += $bound(K0) * $bound(J0) * $bound(X0) * $bound(H0).
    rewrite(X: H,Y: H2,Z: H3) += $bound(H2) * $bound(H3) * $bound(X) * $bound(Y) * $bound(Z) * $bound(H).
    rewrite($Gen1,$Gen2) += $bound($Gen1) * $bound($Gen2).
    word($Gen3,$Gen4,$Gen5) += $bound($Gen4) * $bound($Gen3) * $bound($Gen5).
    """)


def test_oddeven():

    m = Program("""
    oddlen([X|Xs]) :- t(X), evenlen(Xs).
    evenlen([]).
    evenlen([X|Xs]) :- t(X), oddlen(Xs).
    goal :- oddlen(X), evenlen(X).
    """, 't(_).', 'goal.'
    ).type_analysis(Program("""
        """, 't(_).', ''),
        rewrites = """
        """,
        max_depth=7,
    )

    m.assert_equal("""
    goal.   % goal derived because we rounded up

    oddlen([X, $X1, $X2, $X3, $X4, $Trunc | $$Trunc1]) += t($X1) * t(X) * t($X3) * t($X2) * t($X4).
    oddlen([X, $X1, $X2, $X3, $X4]) += t($X3) * t($X2) * t($X1) * t(X) * t($X4).
    oddlen([X, $X1, $X2]) += t($X1) * t(X) * t($X2).
    oddlen([X]) += t(X).

    evenlen([X, $X1, $X2, $X3, $X4, $Trunc | $$Trunc1]) += t($X4) * t(X) * t($X3) * t($X1) * t($X2).
    evenlen([X, $X1, $X2, $X3]) += t($X1) * t($X2) * t(X) * t($X3).
    evenlen([X, $X1]) += t(X) * t($X1).
    evenlen([]).

    """)


def test_huang_sagae():

    p = Program("""
    b(0, 0, 0, 0, 0).

    % Shift: move the head of queue, w[j:k], onto the stack as a singleton tree
    b(L', I, K, H, J) +=
          b(L,I,J,_,H)
        * word(J,K)
        * s(L,L').

    % Reduce left arc: combine the top two trees on the stack, s0 and s1, and replace them with tree s1 <- s0
    b(L', I,K, H",H')
       += b(_, I,J, H",H')
        * b(L, J,K, H',H)
        * lscore(H,H',H")
        * s(L,L').

    % Reduce right arc: combine the top two trees on the stack, s0 and s1, and replace them with tree s1 -> s0
    b(L', I,K, H",H)
       += b(_, I,J, H",H')
        * b(L, J,K, H',H)
        * rscore(H,H',H")
        * s(L,L').

    s(L,L') += word(L,L').

    params: word(_,_); lscore(_,_,_); rscore(_,_,_).

    """)


    input_type = Program("""

    word(I,K) :- n(I), n(K).
    lscore(H, H', H") :- n(H), n(H'), n(H").
    rscore(H, H', H") :- n(H), n(H'), n(H").

    params: n(_).
    """)

    rewrites = """
    n(0).
    """

    s = p.type_analysis(input_type, rewrites)
    s.assert_equal(input_type + """
    b(L',0,K,H,J) += n(J) * n(L') * n(K) * n(H).
        % ^always equal to 0
    s(L,L') += n(L) * n(L').
    """)
    #s.runtime_polynomial(verbose=1)



def test_cky():

    p = Program("""
    phrase(X,I,K) += rewrite(X,Y,Z) * phrase(Y,I,J) * phrase(Z,J,K).
    phrase(X,I,K) += rewrite(X,Y) * phrase(Y,I,K).
    phrase(X,I,K) += rewrite(X,Y) * word(Y,I,K).
    goal += phrase("ROOT", 0, N) * length(N).

    inputs: word(X,I,K); rewrite(X,Y,Z); rewrite(X,Y); length(I).
    outputs: goal.

    """)

    input_type = Program("""
    % TYPE SYSTEM
    %
    % type k: nonterminal
    % type w: terminal
    % type n: position

    word(X,I,K) :- w(X), n(I), n(K).
    rewrite(X,Y,Z) :- k(X), k(Y), k(Z).
    rewrite(X,Y) :- k(X), k(Y).
    rewrite(X,Y) :- k(X), w(Y).
    length(I) :- n(I).

    """, 'k(_). n(_). w(_).', '')


    rewrites = """
    k("ROOT").
    n(0).
    $fail :- k(X), w(X).
    $fail :- k(X), n(X).
    $fail :- w(X), n(X).
    """

    s = p.type_analysis(input_type, rewrites)

    s.assert_equal(input_type + """
    % derived types
    phrase(X, I, K) += k(X) * n(I) * n(K).
    goal.
    """)

    # Suppose there are no preterminal rules, then we cannot derive any phrases
    # nor goal.
    input_type2 = Program("""
    word(X,I,K) :- w(X), n(I), n(K).
    rewrite(X,Y,Z) :- k(X), k(Y), k(Z).
    rewrite(X,Y) :- k(X), k(Y).
    %%% rewrite(X,Y) :- k(X), w(Y).
    length(I) :- n(I).

    inputs: k(_); n(_); w(_).
    """)

    s = p.type_analysis(input_type2, rewrites)
    s.assert_equal(input_type2 + """
    %%%% derived types
    %%% phrase(X, I, K) += k(X) * n(I) * n(K).
    %%% goal.
    """)

    # Suppose the word relation has the wrong argument ordering, then we cannot
    # derive any phrases nor goal.
    input_type3 = Program("""
    %%% word(X,I,K) :- w(X), n(I), n(K).     % want these args
    word(I,X,K) :- w(X), n(I), n(K).         % have these args

    rewrite(X,Y,Z) :- k(X), k(Y), k(Z).
    rewrite(X,Y) :- k(X), k(Y).
    rewrite(X,Y) :- k(X), w(Y).
    length(I) :- n(I).

    inputs: k(_); n(_); w(_).
    """)

    s = p.type_analysis(input_type3, rewrites)
    s.assert_equal(input_type3 + """
    %%%% derived types
    %%% phrase(X, I, K) += k(X) * n(I) * n(K).
    %%% goal.
    """)


def test_graph():

    src = Program("""
    path(S) += start(S).
    path(S') += path(S) * edge(S, S').
    goal += path(S) * stop(S).
    """)

    A = Program("""

    edge(I,J) :- n(I), n(J).
    start(I) :- s(I).
    stop(I) :- e(I).

    """, "n(_). s(_). e(_).", '')

    rewrites = """
    n(I) :- s(I).
    n(I) :- e(I).
    """

    m = src.type_analysis(A, rewrites)

    m.assert_equal("""

    % input types
    stop(I) += e(I), n(I).             % e(I), n(I) is a bit redundant bc e imples n (similarly for s below)
    start(I) += s(I) , n(I).
    edge(I, J) += n(I) * n(J).

    % derived types
    %path(S) += s(S).     % type s ⊆ n given the rewrites
    path(S') += n(S').
    goal.

    """)


def test_simplest():

    src = Program("""
    c1("hi").
    c2("bye").
    const(I) += c1(I) * c2(I).   % never built because c1 ∩ c2 = ∅.

    g(S) += f(S).
    goal += g(S).
    ab(Y) += a(Y) * b(Y).
    h("hi", Y) += a(Y).
    h("bye", Y) += b(Y).
    d(X, Y, Z) += h(X,Y) * h(X,Z).

    """)

    A = Program("""
    a(X) :- a'(X).
    b(X) :- b'(X).
    f(X) :- f'(X).
    """, "a'(_). b'(_). f'(_).")

    rewrites = """
    $fail :- a'(X), b'(X).
    """

    m = src.type_analysis(A, rewrites)

    m.assert_equal("""
    a(X) :- a'(X).
    b(X) :- b'(X).
    f(X) :- f'(X).
    c1("hi").
    c2("bye").

    %ab(Y) += a'(Y) * b'(Y).   % goes to zero because a' and b' do not overlap

    d("bye", Y, Z) :- b'(Y), b'(Z).
    d("hi", Y, Z) :- a'(Y), a'(Z).
    g(S) :- f'(S).
    h("bye", Y) :- b'(Y).
    h("hi", Y) :- a'(Y).
    goal.
    """)


def test_infinite_diagonal():
    # The product of diagonal matrices is an identity matrix

    p = Program("""
    % chain of equalities
    goal(X1,X4) += g(X1,X2) * g(X2,X3) * g(X3,X4).
    g(X,X) += h(X).   % values along the diagonal
    """)

    # types
    input_type = Program("""
    h(X) :- h'(X).
    """, "h'(X).")

    rewrites = """
    """

    S = p.type_analysis(input_type, rewrites)

    S.assert_equal("""
    h(X) += h'(X).
    g(X, X) += h'(X).
    goal(X, X) += h'(X).
    """)


def test_free():

    p = Program("""

    % TODO: In the booleanization conversion, we ought to automatically add the
    % $free delayed constraints.
    f(X,Y).
    f(3,Y).
    f(X,4).
    f(3,4).

    g(h(X,X), p(Y,Y)) += f(X,Y) * p(Y).

    q(X,X',Y,Y') += g(h(X,X'),p(Y,Y')).   % will have X=X' and Y=Y'
    goal += f(X,X).

    """)

    input_type = Program("""
    p(X) :- d(X).

    """, 'd(_).')

    rewrites = """
    d(4).
    """

    m = p.type_analysis(input_type, rewrites)

    # [2021-08-17 Tue] Updated Program to remove rules that cover others
    # (commented out rules below are covered).
    m.assert_equal("""

    f(X,Y) += $free(X), $free(Y).
    f(3,Y) += $free(Y).
    f(X,4) += $free(X).
    f(3,4).

    g(h(3, 3), p(Y, Y)) :- d(Y).
    g(h(X, X), p(Y, Y)) :- d(Y), $free(X).
    % g(h(3, 3), p(4, 4)).
    % g(h(X, X), p(4, 4)) :- $free(X).
    goal.
    p(X) :- d(X).
    % q(3, 3, Y', Y') :- d(Y').
    % q(3, 3, 4, 4).
    % q(X', X', 4, 4) :- $free(X').
    q(X',X',Y',Y') :- d(Y'), $free(X').
    q(3,3,Y',Y') :- d(Y').

    """)


def test_earley():
    #from dyna.benchmarks.earley import Earley
    #b = Earley()

    src = Program("""
    need(s, 0).
    need(X, J) += phrase(_, [X | _], _, J).   % should be `need(..) |= ...`
    phrase(X, Ys, I, I) += rewrite(X, Ys) * need(X, I).                      % approximate should be ?need
    phrase(X, Ys, I, K) += phrase(X, [W | Ys], I, J) * word(W, J, K).
    phrase(X, Ys, I, K) += phrase(X, [Y | Ys], I, J) * phrase(Y, [], J, K).
    goal += phrase(s, [], 0, N) * length(N).
    """)

    types = Program("""

    % typed input relations
%    word(X,I,K) :- k(X), n(I), n(K), (I < K).   % Uncomment for Earley's less than constraints
    word(X,I,K) :- k(X), n(I), n(K).
    length(I) :- n(I).
    rewrite(X,Ys) :- k(X), ks(Ys).

    """, 'k(_). n(_). ks(_). (_ < _).')

    rewrites = """
    % recursive type: a list of elements each of which are type k.
    ks([]).
    ks(Xs) :- ks([X|Xs]).
    k(X) :- ks([X|Xs]).

    k(s).
    n(0).
    $fail :- k(X), n(X).   % k and n do not overlap

    (I < K) :- (I < J), (J < K).
    $fail :- (I < J), (J < I).
    $fail :- (I < I).

    """

    m = src.type_analysis(types, rewrites)

    #p.fc_analysis().show()

    m.assert_equal("""

    % input types
    length(I) :- n(I).
    rewrite(X, Ys) :- k(X), ks(Ys).
    word(X, I, K) :- k(X), n(I), n(K).

    % output types
    goal.
    need(X, J) :- k(X), n(J).
    phrase(X, Ys, J, K) :- k(X), ks(Ys), n(J), n(K).

    """)

#    m.runtime_polynomial(verbose=True)
#    print(m.runtime_polynomial())


def test_slashed_unary_cky():

    p = Program("""
    (p(X0,I0,K0)/p(X0,I0,K0)).
    (p(X,I,K)/p(X0,I0,K0)) += rewrite(X,Y) * p(Y,I,K)/p(X0,I0,K0).
    other(p(X,I,K)) += tag(X, Y) * word(Y,I,K).
    other(p(X,I,K)) += rewrite(X,Y,Z) * p(Y,I,J) * p(Z,J,K).
    p(X,I,K) += (p(X,I,K)/p(X0,I0,K0)) * other(p(X0,I0,K0)).
    goal += other(goal).
    other(goal) += length(N) * p(root, 0, N).

    """, '', 'goal.')

    types = Program("""
    word(X,I,K) :- w(X), n(I), n(K).
    length(I) :- n(I).
    rewrite(X,Y) :- k(X), k(Y).
    tag(X,Y) :- k(X), w(Y).
    rewrite(X,Y,Z) :- k(X), k(Y), k(Z).

    """, 'w(_). k(_). n(_).')

    rewrites = """
    k(root).
    n(0).
    $fail :- n(X), k(X).
    k(X) :- $free(X), k(X).
    n(X) :- $free(X), n(X).
    """

    m = p.type_analysis(types, rewrites)
    m.assert_equal("""

    % derived types
%    (p(X0, I0, K0) / p(X0, I0, K0)).                   % base case
%    (p(X, I, K) / p(X', I, K)) :- k(X), k(X').         % I=I', J=J'
    other(p(X, I, K)) :- k(X), n(I), n(K).
    other(goal).
    goal.
    p(X0, I0, K0) += k(X0) * n(I0) * n(K0).

    (p(X, I, K) / p(X, I, K)) :- $free(X) * $free(I) * $free(K).
    (p(X, I, K) / p(X', I, K)) :- k(X) * k(X') * $free(I) * $free(K).

    % input types
    word(X,I,K) :- w(X), n(I), n(K).
    length(I) :- n(I).
    rewrite(X,Y) :- k(X), k(Y).
    tag(X,Y) :- k(X), w(Y).
    rewrite(X,Y,Z) :- k(X), k(Y), k(Z).

    """)

#    q = m.runtime_polynomial(verbose=1)


def test_pda():

    p = Program("""

    % inital stack is empty
    pda([],0) += 1.

    % shift
    pda([X|Rest],K) += pda(Rest,J) * rewrite(X,Y) * word(Y,J,K).

    % reduce
    pda([X|Rest],K) += pda([Z,Y|Rest],K) * rewrite(X,Y,Z).

    % parse of the entire input
    goal += pda([s],N) for length(N).

    """, 'rewrite(X,Y). rewrite(X,Y,Z). word(X,I,K). length(N).')


    # TODO: need a ks type.  Probably have to manually initialize pda to have
    # that type.  Otherwise, we will just run forever enumerating lists of every
    # length.
    input_type = Program("""

    rewrite(X,Y) :- k(X), k(Y).
    rewrite(X,Y,Z) :- k(X), k(Y), k(Z).
    word(X,I,K) :- k(X), n(I), n(K).
    length(I) :- n(I).

%    ks([]).
%    ks([K|Ks]) :- k(K), ks(Ks).

    pda(Xs, K) :- ks(Xs), n(K).

    """, 'k(_). n(_). ks(_).')

    rewrites = """
    k(s).
    n(0).

    ks([]).
    k(X) :- ks([X|Xs]).
    ks(Xs) :- ks([X|Xs]).

    """

    m = p.type_analysis(input_type, rewrites, max_depth=5)

    m.assert_equal("""
    rewrite(X, Y) += k(X) * k(Y).
    rewrite(X, Y, Z) += k(Z) * k(X) * k(Y).
    word(X, I, K) += n(I) * n(K) * k(X).
    length(I) += n(I).
    pda(Xs, K) += ks(Xs) * n(K).
    goal.
    """)


def test_arc_standard():

    p = Program("""

    p(I,I,K) += word(I,K).   % no need to give the terminal symbol in this formulation
    p(I,H2,K) += p(I,H1,J) * p(J,H2,K) * score(H1 <~ H2).
    p(I,H1,K) += p(I,H1,J) * p(J,H2,K) * score(H1 ~> H2).

    goal += p(0,0,N) * len(N).
    """, 'word(_,_,_). len(_). score(_).', 'goal.')

    input_type = Program("""
    score(H1 ~> H2) :- n(H1), n(H2).
    score(H1 <~ H2) :- n(H1), n(H2).
    word(I,K) :- n(I), n(K).
    len(N) :- n(N).

    """, 'n(_).')

    rewrites = """
    n(0).
    """

    m = p.type_analysis(input_type, rewrites)

    # [2021-08-17 Tue] Updated Program to remove rules that cover others
    # (commented out rules below are covered).
    m.assert_equal("""
    p(I, H, K) :- n(I), n(H), n(K).
    score(H1 ~> H2) :- n(H1), n(H2).
    score(H1 <~ H2) :- n(H1), n(H2).
    word(I,K) :- n(I), n(K).
    len(N) :- n(N).
    goal.
    """)

#    q = m.runtime_polynomial(verbose=1)
#    assert str(q) == '2 n⁵ + 4 n² + 2 n', q

#    opt = p.beam_binarize(1000,10).best
#    m1 = opt.type_analysis(input_type, rewrites)
#    q = str(m1.runtime_polynomial(verbose=1))
#    assert q == '4 n⁴ + 4 n² + 2 n', q


def test_arc_eager():

    # See figure 7 and section 5.3 of https://aclanthology.org/P11-1068.pdf
    p = Program("""

    p(I,I^0,K) += word(I,K).
    p(I,I^1,K) += word(I,K).

    p(I,H^B,K) += p(I,H^B,J) * p(J,H'^0,K) * shift(I, J) * score(J <~ K).
    p(I,H^B,K) += p(I,H^B,J) * p(J,H'^1,K) * score(I ~> J) * reduce(J, K).

    goal += p(0,0^0,N) * len(N).
    """, 'word(_,_). len(_). shift(_,_). reduce(_,_). score(_).', 'goal.')

    input_type = Program("""
    score(H1 ~> H2) :- n(H1), n(H2).
    score(H1 <~ H2) :- n(H1), n(H2).
    shift(H1, H2) :- n(H1), n(H2).
    reduce(H1, H2) :- n(H1), n(H2).
    word(I,K) :- n(I), n(K).
    len(N) :- n(N).

    """, 'n(_).')

    rewrites = """
    n(0).
    """

    # Two interesting things happen here.  We infer the finite domain for B.  We
    # infer that I=H in every p(I,H^B,K) item.
    m = p.type_analysis(input_type, rewrites)
    m.assert_equal(input_type + """
    p(I, I^0, K) :- n(I), n(K).
    p(I, I^1, K) :- n(I), n(K).
    goal.
    """)


def test_cky_less():
    """
    This example is pretty cool.  It infers---quite easily--that I<K in
    the input (words(I,X,K) is results in I<K in phrase(I,X,K).
    """

    p = Program("""
    phrase(X,I,K) += rewrite(X,Y,Z) * phrase(Y,I,J) * phrase(Z,J,K).
    phrase(X,I,K) += rewrite(X,Y) * phrase(Y,I,K).
    phrase(X,I,K) += rewrite(X,Y) * word(Y,I,K).
    goal += phrase("ROOT", 0, N) * length(N).

    inputs: word(X,I,K); rewrite(X,Y,Z); rewrite(X,Y); rewrite(X,Y); length(I).
    outputs: goal.
    """)

    input_type = Program("""
    % TYPE SYSTEM
    %
    % type k: nonterminal
    % type w: terminal
    % type n: position

    word(X,I,K) :- w(X), n(I), n(K), (I < K).
    rewrite(X,Y,Z) :- k(X), k(Y), k(Z).
    rewrite(X,Y) :- k(X), k(Y).
    rewrite(X,Y) :- k(X), w(Y).
    length(I) :- n(I).

    """, 'k(_). n(_). w(_). (_ < _).', '')

    rewrites = """
    k("ROOT").
    $fail :- k(X), w(X).
    $fail :- k(X), n(X).
    n(0).
    (I < K) :- (I < J), (J < K).
    $fail :- (I < J), (J < I).
    $fail :- (I < I).
    """

    s = p.type_analysis(input_type, rewrites)

    s.assert_equal("""
    word(X, I, K) += n(I) * (I < K) * n(K) * w(X).
    rewrite(X, Y, Z) += k(Y) * k(X) * k(Z).
    rewrite(X, Y) += k(X) * k(Y).
    rewrite(X, Y) += w(Y) * k(X).
    length(I) += n(I).
    phrase(X, I, K) += (I < K) * k(X) * n(K) * n(I).
    goal.
    """)


def test_slash_binary_cky():

    cky = Program("""
    goal += c(s,0,N) * len(N).
    c(A,I,K) += rewrite(A,B) * word(B,I,K).
    c(A,I,K) += rewrite(A, B, C) * c(B,I,J) * c(C,J,K).

    """, 'rewrite(_,_,_). word(_,_,_). len(_).', 'goal.')

    input_type = Program("""

    word(X,I,K) :- w(X), n(I), n(K).
    rewrite(X,Y,Z) :- k(X), k(Y), k(Z).
    rewrite(X,Y) :- k(X), k(Y).
    rewrite(X,Y) :- k(X), w(Y).
    len(I) :- n(I).

    """, 'k(_). n(_). w(_).', '')

    rewrites = """
%    k(s).
%    n(0).

    $fail :- k(X), w(X).
    """

    sl = cky.slash("c(B',I',J')", positions={2: 1})

    S = sl.type_analysis(input_type, rewrites)

    S.assert_equal("""
    (c(B', I', J') / c(B', I', J')) += $free(J') * $free(I') * $free(B').
    (c(A, I', K) / c(B', I', J')) += k(B') * n(J') * $free(I') * k(A) * n(K).
%    $other(goal).
    $other(c(A, I, K)) += n(K) * k(A) * n(I).
    c($X0, I', $X2) += n($X2) * n(I') * k($X0).
    goal.
    word(X, I, K) += w(X) * n(K) * n(I).
    rewrite(X, Y, Z) += k(Y) * k(Z) * k(X).
    rewrite(X, Y) += k(X) * k(Y).
    rewrite(X, Y) += w(Y) * k(X).
    len(I) += n(I).
    """)


def test_word_list():
    p = Program("""

    buffer(N,[]) += length(N).
    buffer(J,[W|Ws]) += word(W,J,K) * buffer(K,Ws).

    """, 'word(_,_,_).')

    input_type = Program("""

    word(W,I,K) :- w(W), n(I), n(K).
    length(N) :- n(N).

    buffer(J,Ws) :- n(J), ws(Ws).  % initialization

    """, 'n(_). ws(_). w(_).', '')

    #print(p(PAPA_DATA).user_query('buffer(_,_)'))

    rewrites = """
    ws([]).
    w(W) :- ws([W|Ws]).
    ws(Ws) :- ws([W|Ws]).
    """

    S = p.type_analysis(input_type, rewrites, max_depth=5)

    S.assert_equal("""
    buffer(J,Ws) += n(J) * ws(Ws).
    length(N) += n(N).
    word(W,I,K) += n(I) * w(W) * n(K).
    """)


if __name__ == '__main__':
    from arsenal.testing_framework import TestingFramework
    F = TestingFramework(globals())
    import dyna.analyze.types
    F.cli.add_argument('--debug', type=int, default=0)
    dyna.analyze.types.debug(F.cli.parse_args().debug)
    F.run()
