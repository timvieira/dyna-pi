"""
Tests for range-restriction normalization
(docs/range-restriction-normalization.md).

M1: the openness fixpoint (`open_types`) and the refined per-rule
range-restriction check (`is_rule_range_restricted`).
M2-M5: the `RangeRestrictionNormalization` transform — projection + recovery +
multiplicity (M2-M3), residue isolation (M4), and the active-domain escape (M5).
"""

from dyna import Program, term_vars, Boolean
from dyna.analyze.range_restriction import (
    open_types, has_free, bindable_vars,
    is_rule_range_restricted, is_range_restricted,
)
from dyna.transform.range_restriction import RangeRestrictionNormalization


def E1():
    return Program("""
    f(X) += 3.
    goal += f(X).
    outputs: goal.
    """)


def E2():
    return Program("""
    temp(X0, X0) += 1.
    temp(X, X0)  += rewrite(X, Y) * temp(Y, X0).
    inputs: rewrite(X, Y).
    outputs: temp(X, X0).
    """)


def E3():
    return Program("""
    f(X) += 3.
    out(X) += f(X).
    outputs: out(X).
    """)


def E5():
    return Program("""
    f(X) += g(Y) * (X > Y).
    goal += f(X).
    inputs: g(Y).
    outputs: goal.
    """)


def E6():
    return Program("""
    temp(pair(X0, X0)) += 1.
    temp(pair(X, X0))  += rewrite(X, Y) * temp(pair(Y, X0)).
    inputs: rewrite(X, Y).
    outputs: temp(W).
    """)


def open_heads(p, **kwargs):
    "Render the open types' heads as a set of strings (variable names normalized)."
    return {str(t.head) for t in open_types(p, **kwargs)}


def test_M1_E1_projection():
    # (the only) primitive source of openness: head var absent from body
    ts = open_types(E1())
    assert len(ts) == 1
    [t] = ts
    assert t.head.fn == 'f' and t.head.arity == 1
    assert has_free(t)


def test_M1_E2_threaded_diagonal():
    # only the reflexive base type is open; the recursive type is closed
    ts = open_types(E2())
    assert len(ts) == 1
    [t] = ts
    # the diagonal is one shared variable, not two independent open slots
    assert t.head.fn == 'temp' and t.head.arity == 2
    a, b = t.head.args
    assert a is b or str(a) == str(b)
    assert len(term_vars(t.head)) == 1


def test_M1_E3_propagation():
    # failure-case 3: openness propagates through consumption (out += f)
    assert open_heads(E3()) == {'f(X)', 'out(X)'}


def test_M1_E5_test_only_detection():
    # X occurs only in a test: NOT pass-through (no $free type — the value of
    # f(X) depends on X), but the rule is NOT range-restricted either; the
    # syntactic check wrongly accepts it (the E5 trap, spec Section 8).
    p = E5()
    assert open_types(p) == []
    assert p.is_range_restricted()          # syntactic: wrong
    assert not is_range_restricted(p)       # refined: right
    [rf, _] = p.rules
    assert rf.head.fn == 'f'
    assert not is_rule_range_restricted(p, rf)


def test_M1_E6_nested_sharing_canary():
    # E2 folded inside one argument: the analysis must keep the X0=X0 sharing
    # through widening (one $free variable, ground pair skeleton retained)
    ts = open_types(E6())
    assert len(ts) == 1
    [t] = ts
    [arg] = t.head.args
    assert arg.fn == 'pair'
    a, b = arg.args
    assert a is b or str(a) == str(b)
    assert len(term_vars(t.head)) == 1


def test_M1_depth():
    # open variable nested in a structured argument: skeleton f(g(.)) retained
    p = Program("""
    f(g(X)) += 3.
    goal += f(W).
    outputs: goal.
    """)
    ts = open_types(p)
    assert len(ts) == 1
    [t] = ts
    [arg] = t.head.args
    assert arg.fn == 'g'
    assert has_free(t)


def test_M1_list_tail():
    # openness in recursive structure (a list tail position)
    p = Program("""
    f([X|Xs]) += 3.
    goal += f(L).
    outputs: goal.
    """)
    ts = open_types(p)
    assert len(ts) == 1
    [t] = ts
    assert has_free(t)


def test_M1_input_declared_ground():
    # an input declaration is a binding source: h arrives ground, so the
    # consumer is range-restricted and nothing is open
    p = Program("""
    out(X) += h(X).
    inputs: h(X).
    outputs: out(X).
    """)
    assert open_types(p) == []
    assert is_range_restricted(p)


def test_M1_input_declared_open():
    # an input *type* with an explicit $free position is open by declaration
    # (no rule derives it) — the base case the body-only seeds miss
    p = Program("""
    out(X) += h(X).
    inputs: h(X).
    outputs: out(X).
    """)
    ts = open_types(p, input_type=Program('h(X) += $free(X).'))
    assert {t.head.fn for t in ts} >= {'h'}
    # and the openness propagates to the consumer's head
    assert 'out' in {t.head.fn for t in ts}


def test_M1_metamorphic_rename():
    # invariance under renaming functors (Section 3.2)
    p = E3()
    q = Program("""
    zap(X) += 3.
    quux(X) += zap(X).
    outputs: quux(X).
    """)
    assert {(t.head.fn, t.head.arity, has_free(t)) for t in open_types(p)} == \
           {('f', 1, True), ('out', 1, True)}
    assert {(t.head.fn, t.head.arity, has_free(t)) for t in open_types(q)} == \
           {('zap', 1, True), ('quux', 1, True)}


def test_M1_metamorphic_wrap():
    # invariance under wrapping in a dummy functor: f(X) -> w(f(X))
    p = Program("""
    f(w(X)) += 3.
    out(X) += f(w(X)).
    outputs: out(X).
    """)
    ts = open_types(p)
    assert {t.head.fn for t in ts} == {'f', 'out'}
    # the wrapped open occurrence keeps its skeleton
    [tf] = [t for t in ts if t.head.fn == 'f']
    [arg] = tf.head.args
    assert arg.fn == 'w'


def test_M1_metamorphic_thread():
    # invariance under threading a dummy argument
    p = Program("""
    f(X, D) += g(D).
    out(X, D) += f(X, D).
    g(c) += 1.
    outputs: out(X, D).
    """)
    ts = open_types(p)
    # X is open in both f and out; D is bound by g
    assert {t.head.fn for t in ts} == {'f', 'out'}
    for t in ts:
        frees = {c.args[0] for c in t.body if c.fn == '$free'}
        assert len(frees) == 1


def test_M1_bindable_vars_builtins():
    # `is` is a binder (the engine inverts it); comparisons are tests
    p = Program("""
    f(X) += g(Y) * (X is Y + 1).
    outputs: f(X).
    """)
    [r] = p.rules
    assert term_vars(r.head) <= bindable_vars(p, r)
    assert is_range_restricted(p)

    q = Program("""
    f(X) += g(Y) * (X > Y).
    outputs: f(X).
    """)
    [r] = q.rules
    assert not (term_vars(r.head) <= bindable_vars(q, r))


#_______________________________________________________________________________
# M2-M5: the normalization transform


def test_M2_E1_infinite_multiplicity():
    # reproduces the test_infinite_multiplicity value: the summed open
    # variable becomes a Semiring.multiple(inf) witness factor
    p = E1()
    q = p.normalize_range_restriction()
    q.assert_equal("""
    goal += goal_1.
    f_0 += 3.
    goal_1 += f_0 * ∞.
    """)
    assert q.residual_layer.rules == []
    p.sol().assert_equal_query('goal', float('inf'))
    q.sol().assert_equal_query('goal', float('inf'))


def test_M2_E2_threaded_no_factor():
    # the threaded variable is renamed away on both sides: NO multiplicity
    # factor, and the reflexive diagonal survives as the recovery rule
    p = E2()
    q = p.normalize_range_restriction()
    q.assert_equal("""
    rewrite_0(X,Y) += rewrite(X,Y).
    temp(X,X0) += temp_1(X,X0).
    temp(X0,X0) += temp_2.
    temp_2 += 1.
    temp_1(X,X0) += rewrite_0(X,Y) * temp_1(Y,X0).
    temp_1(X,X0) += rewrite_0(X,X0) * temp_2.
    """)
    # exactly the spec's E2: diagonal recovery rule is the only residue
    [r] = q.residual_layer.rules
    a, b = r.head.args
    assert str(a) == str(b)

    D = 'rewrite(a,b) += 0.5. rewrite(b,c) += 0.25.'
    ps, qs = (p + D).sol(), (q + D).sol()
    for query in ['temp(a,c)', 'temp(a,a)', 'temp(b,b)', 'temp(a,b)']:
        want = ps.user_query(query)
        qs.assert_equal_query(query, want)


def test_M2_E6_nested_diagonal():
    # E6 must behave exactly like E2: same residue shape, same values
    p = E6()
    q = p.normalize_range_restriction()
    [r] = q.residual_layer.rules
    [arg] = r.head.args
    assert arg.fn == 'pair'
    a, b = arg.args
    assert str(a) == str(b)

    D = 'rewrite(a,b) += 0.5.'
    ps, qs = (p + D).sol(), (q + D).sol()
    for query in ['temp(pair(a,b))', 'temp(pair(a,a))', 'temp(pair(b,b))']:
        qs.assert_equal_query(query, ps.user_query(query))


def test_M3_transform_is_a_transformed_program():
    from dyna import TransformedProgram
    q = E1().normalize_range_restriction()
    assert isinstance(q, RangeRestrictionNormalization)
    assert isinstance(q, TransformedProgram)
    assert q.parent is not None


def test_M3_E5_not_projected():
    # A test-only variable is non-bindable but NOT pass-through: the value of
    # f(X) depends on X, so projecting it would corrupt ground queries.  The
    # rule is irreducible residue without an active domain; the refined check
    # must report it (the syntactic check passes it — the E5 trap).
    p = E5()
    q = p.normalize_range_restriction()
    # the engine layer is clean, and the f rule is the residue
    assert is_range_restricted(q.engine_layer)
    [r] = q.residual_layer.rules
    assert r.head.fn == 'f'
    # the trap: the syntactic program-level check would have declared success
    assert p.is_range_restricted()
    assert not is_range_restricted(q)

    # the normalization leaves E5's rules untouched (no unsound projection),
    # so the solved charts coincide — including the delayed test, which is
    # what projecting X would have destroyed (f(2) must be 0 when g(3)=1,
    # but a projected f_open would have given every f(_) the value 1)
    D = 'g(3) += 1.0.'
    ps, qs = (p + D).sol(), (q + D).sol()
    qs.assert_equal(ps)


def test_M3_engine_layer_refined_everywhere():
    # DoD #3 (refined check on the engine layer) on all worked examples
    for make in [E1, E2, E3, E5, E6]:
        q = make().normalize_range_restriction()
        assert is_range_restricted(q.engine_layer), make.__name__
        for r in q.residual_layer.rules:
            assert not is_rule_range_restricted(q, r)


def test_M4_E3_residue_isolation():
    # E3: exactly one residual rule — the recovery rule feeding the output
    p = E3()
    q = p.normalize_range_restriction()
    q.assert_equal("""
    out(X) += out_1.
    f_0 += 3.
    out_1 += f_0.
    """)
    [r] = q.residual_layer.rules
    assert r.head.fn == 'out'
    assert q.is_output(r.head)
    # non-recursive: its body consumes only the projected engine item
    assert all(not b.fn == 'out' for b in r.body if hasattr(b, 'fn'))

    ps, qs = p.sol(), q.sol()
    qs.assert_equal_query('out(z)', ps.user_query('out(z)'))


def test_M4_E1_empty_residue():
    # DoD #4: residue empty exactly when no free variable reaches an output
    assert E1().normalize_range_restriction().residual_layer.rules == []
    assert len(E3().normalize_range_restriction().residual_layer.rules) == 1


def test_M5_E4_adom_escape():
    # Step E: adom removes the residue; witness counts become |adom|
    p = E3()
    q = p.normalize_range_restriction(adom='adom')
    q.assert_equal("""
    out(X) += out_1 * adom(X).
    f_0 += 3.
    out_1 += f_0.
    """)
    assert q.residual_layer.rules == []
    assert is_range_restricted(q)
    assert q.is_range_restricted()

    # under active-domain semantics, out(z) = 3 for z in adom
    D = 'adom(a) += 1.0. adom(b) += 1.0.'
    qs = (q + D).sol()
    qs.assert_equal_query('out(a)', 3.0)
    qs.assert_equal_query('out(b)', 3.0)


def test_M5_E1_adom_multiplicity():
    # E1's inf becomes |adom|: goal = |adom| * 3
    p = E1()
    q = p.normalize_range_restriction(adom='adom')
    assert is_range_restricted(q)
    D = 'adom(a) += 1.0. adom(b) += 1.0.'
    (q + D).sol().assert_equal_query('goal', 6.0)


def test_M5_E5_adom():
    # the irreducible test-constrained rule becomes range-restricted with adom
    p = E5()
    q = p.normalize_range_restriction(adom='adom')
    assert q.residual_layer.rules == []
    assert is_range_restricted(q)
    # f(X) = sum_Y g(Y)*[X>Y] over X in adom: with g(3)=1, f(5)=1 and f(2)=0
    D = 'g(3) += 1.0. adom(2) += 1.0. adom(5) += 1.0.'
    qs = (q + D).sol()
    qs.assert_equal_query('f(5)', 1.0)
    qs.assert_equal_query('goal', 1.0)


def test_DoD6_idempotent_multiplicity():
    # the witness factor is produced via Semiring.multiple, so it collapses
    # to `one` in an idempotent semiring rather than being a literal inf
    assert Boolean.multiple(float('inf')) == Boolean.one
    p = Program("""
    f(X) += 1.
    goal += f(X).
    outputs: goal.
    """, semiring=Boolean)
    q = p.normalize_range_restriction()
    # the correction constant in the normalized program is Boolean.one
    [r] = [r for r in q.rules if r.head.fn.startswith('goal_')]
    consts = [b for b in r.body if q.is_const(b)]
    assert consts == [Boolean.one]


def test_DoD2_equivalence_geom():
    # a richer program: lifted geometric series (from the abbreviation tests)
    p = Program("""
    x(I) += 1.
    x(I) += 0.5 * x(I).
    outputs: x(_).
    """)
    q = p.normalize_range_restriction()
    assert is_range_restricted(q.engine_layer)
    ps, qs = p.sol(), q.sol()
    qs.assert_equal_query('x(j)', ps.user_query('x(j)'))


def test_M3_input_declared_open_transform():
    # Section 3.1 through the transform: an input type declaring h's position
    # $free is a Step A base case with no deriving rule; the summing consumer
    # gets the inf witness factor and the engine layer is range-restricted
    p = Program("""
    goal += h(X).
    inputs: h(X).
    outputs: goal.
    """)
    q = p.normalize_range_restriction(input_type=Program('h(X) += $free(X).'))
    assert q.residual_layer.rules == []
    assert is_range_restricted(q.engine_layer)
    D = 'h(X) += 5.'   # the open input fact the declaration promised
    ps, qs = (p + D).sol(), (q + D).sol()
    qs.assert_equal_query('goal', ps.user_query('goal'))


def test_DoD2_equivalence_path():
    # recursion through a reflexive open diagonal (E2's shape) consumed
    # ground at the output: the residue disappears into the engine layer
    p = Program("""
    path(I,I) += 1.
    path(I,K) += path(I,J) * edge(J,K).
    goal += path(I,K) * start(I) * stop(K).
    inputs: edge(J,K); start(I); stop(K).
    outputs: goal.
    """)
    q = p.normalize_range_restriction()
    assert is_range_restricted(q.engine_layer)
    D = """
    edge(a,b) += 0.5. edge(b,c) += 0.5. edge(a,c) += 0.25.
    start(a) += 1.0. stop(c) += 1.0.
    """
    ps, qs = (p + D).sol(), (q + D).sol()
    qs.assert_equal_query('goal', ps.user_query('goal'))


#_______________________________________________________________________________
# Post-condition checks / warnings


def test_postcondition_no_warning_on_clean_examples():
    # the worked examples all converge cleanly and produce only genuine
    # residue, so none of them should warn (no false positives)
    import warnings
    for make in [E1, E2, E3, E5, E6]:
        with warnings.catch_warnings():
            warnings.simplefilter('error')   # any warning fails the test
            q = make().normalize_range_restriction()
            assert q.converged
    # adom escape is also clean
    with warnings.catch_warnings():
        warnings.simplefilter('error')
        E3().normalize_range_restriction(adom='adom')
        E5().normalize_range_restriction(adom='adom')


def test_postcondition_warns_on_nonconvergence():
    # starve the loop: max_passes=0 means it never projects, so an open
    # program comes back unconverged and the warning fires
    import pytest
    with pytest.warns(UserWarning, match='did not converge'):
        q = E3().normalize_range_restriction(max_passes=0)
    assert not q.converged


def test_postcondition_E5_residue_is_recognized():
    # the E5 delayed-test rule is *expected* residue, so it must NOT trip the
    # residue-shape warning even though it is non-range-restricted
    q = E5().normalize_range_restriction()
    [r] = q.residual_layer.rules
    assert RangeRestrictionNormalization._is_delayed_test(q, r)


def test_postcondition_E3_residue_is_recovery():
    q = E3().normalize_range_restriction()
    [r] = q.residual_layer.rules
    assert RangeRestrictionNormalization._is_recovery(q, r)


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
