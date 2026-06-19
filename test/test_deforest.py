from dyna import Program, deforest_difference_lists


def test_difference_list_intersection_to_suffix_spans():
    p = Program("""
    inputs: source_string(_); root(_); rule_term(_,_); rule_bin(_,_,_); eq(_,_).
    outputs: goal.

    gen(A, Acc, [W|Acc]) += rule_term(A, W).
    gen(A, Acc, X) += rule_bin(A, B, C) * gen(C, Acc, Mid) * gen(B, Mid, X).

    equal([], []).
    equal([X|Xs], [Y|Ys]) += equal(Xs, Ys) * eq(X, Y).

    goal += root(S) * gen(S, [], Str) * source_string(In) * equal(Str, In).
    """)

    q = deforest_difference_lists(p)

    q.assert_equal("""
    $suffix(In) += source_string(In).
    $suffix(Rest) += $suffix([V|Rest]).

    $span(A, [V|Acc], Acc) += $suffix([V|Acc]) * rule_term(A, W) * eq(W, V).
    $span(A, X, Acc) += rule_bin(A, B, C) * $span(B, X, Mid) * $span(C, Mid, Acc).

    goal += root(S) * source_string(In) * $span(S, In, []).
    """)

    assert all(r.head.fn != 'gen' for r in q if hasattr(r.head, 'fn'))
    assert all(r.head.fn != 'equal' for r in q if hasattr(r.head, 'fn'))


def test_difference_list_deforestation_preserves_extra_factors():
    p = Program("""
    inputs: source_string(_); root(_); rule_term(_,_); rule_bin(_,_,_); eq(_,_); ok(_).
    outputs: goal.

    gen(A, Acc, [W|Acc]) += rule_term(A, W) * ok(A).
    gen(A, Acc, X) += rule_bin(A, B, C) * gen(C, Acc, Mid) * gen(B, Mid, X).

    equal([], []).
    equal([X|Xs], [Y|Ys]) += equal(Xs, Ys) * eq(X, Y).

    goal += root(S) * gen(S, [], Str) * source_string(In) * equal(Str, In).
    """)

    q = deforest_difference_lists(p)

    q.assert_equal("""
    $suffix(In) += source_string(In).
    $suffix(Rest) += $suffix([V|Rest]).

    $span(A, [V|Acc], Acc) += $suffix([V|Acc]) * rule_term(A, W) * eq(W, V) * ok(A).
    $span(A, X, Acc) += rule_bin(A, B, C) * $span(B, X, Mid) * $span(C, Mid, Acc).

    goal += root(S) * source_string(In) * $span(S, In, []).
    """)
