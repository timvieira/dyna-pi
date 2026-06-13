"""
Tests for the phantom-gated range-restriction normalization
(dyna/transform/rr_phantom.py).

Unlike the abbreviate-based transform, projection here is gated by a *provably
sound* phantom-position analysis (head-only, single-occurrence, unconstrained,
propagated), so it never projects a diagonal or a constrained position.  The
load-bearing regression is `test_startpath3_is_sound`: the abbreviate+usefulness
path drops the reflexive diagonal `path(I,I)` and computes all-zero paths; this
system refuses to project it and is therefore correct.
"""

from dyna import Program
from dyna.transform.rr_phantom import phantom_positions, RangeRestrictionPhantom
from dyna.analyze.range_restriction import is_range_restricted


def diff_ok(src, D, queries):
    "True iff the phantom transform agrees with the original on every query."
    p = Program(src)
    q = RangeRestrictionPhantom(p)
    ps, qs = (p + Program(D)).sol(), (q + Program(D)).sol()
    for query in queries:
        if [str(x) for x in ps.user_query(query)] != [str(x) for x in qs.user_query(query)]:
            return False
    return True


# ---------------------------------------------------------------- the analysis

def test_phantom_excludes_diagonals_and_constraints():
    # diagonals and test-only positions are never phantom
    assert phantom_positions(Program('f(X) += 3. goal += f(X). outputs: goal.')) == {('f', 1, 0)}
    assert phantom_positions(Program('temp(X0,X0) += 1. outputs: temp(A,B).')) == set()
    assert phantom_positions(Program(
        'path(I,I). path(I,K) += path(I,J)*edge(J,K). inputs: edge(I,J). outputs: path(I,K).')) == set()
    assert phantom_positions(Program(
        'f(X) += g(Y)*(X>Y). goal += f(X). inputs: g(Y). outputs: goal.')) == set()


def test_phantom_propagates_through_chains():
    P = phantom_positions(Program('a(X)+=3. b(X)+=a(X). c(X)+=b(X). out(X)+=c(X). outputs: out(X).'))
    assert P == {('a', 1, 0), ('b', 1, 0), ('c', 1, 0), ('out', 1, 0)}


def test_phantom_declines_mixed_case():
    # f(1)/f(X): position is a constant in one rule, so not phantom (conservative)
    assert phantom_positions(Program('f(1)+=2. f(X)+=3. goal+=f(X). outputs: goal.')) == set()


# --------------------------------------------------------- soundness (values)

def test_startpath3_is_sound():
    # THE regression: abbreviate+usefulness drops path(I,I) and yields all zeros.
    # The phantom transform refuses to project the diagonal, so values are exact.
    src = 'path(I,I). path(I,K) += path(I,J)*edge(J,K). inputs: edge(I,J). outputs: path(I,K).'
    D = 'edge(a,b)+=1. edge(b,c)+=1.'
    assert diff_ok(src, D, ['path(a,a)', 'path(b,b)', 'path(c,c)',
                            'path(a,b)', 'path(a,c)', 'path(c,a)'])
    # and concretely: the diagonal is non-zero (the bug was all-zeros)
    q = RangeRestrictionPhantom(Program(src))
    qs = (q + Program(D)).sol()
    qs.assert_equal_query('path(a,a)', 1.0)
    qs.assert_equal_query('path(a,c)', 1.0)


def test_E1_projection_and_multiplicity():
    src = 'f(X) += 3. goal += f(X). outputs: goal.'
    assert diff_ok(src, '', ['goal'])
    Program(src).sol().assert_equal_query('goal', float('inf'))
    RangeRestrictionPhantom(Program(src)).sol().assert_equal_query('goal', float('inf'))


def test_E2_E6_diagonals_preserved():
    e2 = 'temp(X0,X0) += 1. temp(X,X0) += rewrite(X,Y)*temp(Y,X0). inputs: rewrite(X,Y). outputs: temp(X,X0).'
    assert diff_ok(e2, 'rewrite(a,b)+=0.5. rewrite(b,c)+=0.25.',
                   ['temp(a,a)', 'temp(a,b)', 'temp(a,c)', 'temp(b,b)'])
    e6 = ('temp(pair(X0,X0)) += 1. temp(pair(X,X0)) += rewrite(X,Y)*temp(pair(Y,X0)). '
          'inputs: rewrite(X,Y). outputs: temp(W).')
    assert diff_ok(e6, 'rewrite(a,b)+=0.5.',
                   ['temp(pair(a,a))', 'temp(pair(a,b))', 'temp(pair(b,b))'])


def test_E3_propagation_values():
    assert diff_ok('f(X) += 3. out(X) += f(X). outputs: out(X).', '', ['out(z)', 'out(a)'])


def test_diagonal_battery_values():
    assert diff_ok('q(X,X) += 2. q(X,Y) += edge(X,Y). out(A,B) += q(A,B). inputs: edge(X,Y). outputs: out(A,B).',
                   'edge(a,b)+=1.', ['out(a,a)', 'out(b,b)', 'out(c,c)', 'out(a,b)'])
    assert diff_ok('q(X,X,X) += 2. q(X,Y,Z) += e(X,Y,Z). out(A,B,C) += q(A,B,C). inputs: e(X,Y,Z). outputs: out(A,B,C).',
                   'e(a,b,c)+=1.', ['out(a,a,a)', 'out(d,d,d)', 'out(a,b,c)'])


def test_engine_layer_range_restricted():
    for src in ['f(X) += 3. out(X) += f(X). outputs: out(X).',
                'a(X)+=3. b(X)+=a(X). out(X)+=b(X). outputs: out(X).']:
        q = RangeRestrictionPhantom(Program(src))
        assert is_range_restricted(q.engine_layer)


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
