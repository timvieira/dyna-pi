"""
Tests for the consolidated sound range-restriction normalization
(dyna/analyze/range_restriction_normalize.py).

Covers the three layers: the phantom analysis (sound + invariant), the phantom
projection, the value-split (constant-overlap), and the combined normalizer.
The load-bearing regression is `test_startpath3_sound`: abbreviate drops the
reflexive diagonal `path(I,I)` (all-zero paths); this refuses to project it.
"""

from dyna import Program
from dyna.analyze.range_restriction import is_range_restricted
from dyna.analyze.range_restriction_normalize import (
    phantom_paths, PhantomProjection, ValueSplit, RangeRestrictionNormalizer,
)


def diff_ok(p, q, queries, D=''):
    ps, qs = (p + Program(D)).sol(), (q + Program(D)).sol()
    return all([str(x) for x in ps.user_query(qy)] == [str(x) for x in qs.user_query(qy)]
               for qy in queries)


# ------------------------------------------------ analysis: sound + invariant

def test_phantom_paths_invariant_under_wrapping():
    assert phantom_paths(Program('f(X) += 3. goal += f(X). outputs: goal.')) == {('f', 1, (0,))}
    assert phantom_paths(Program('g(w(X)) += 3. goal += g(w(X)). outputs: goal.')) == {('g', 1, (0, 0))}
    assert phantom_paths(Program(
        'item(d,f(X)) += 3. goal += item(d,f(X)). outputs: goal.')) == {('item', 2, (1, 0))}


def test_phantom_paths_excludes_diagonals():
    for src in ['temp(X0,X0) += 1. outputs: temp(A,B).',
                'path(I,I). path(I,K) += path(I,J)*edge(J,K). inputs: edge(I,J). outputs: path(I,K).',
                'f(X) += g(Y)*(X>Y). goal += f(X). inputs: g(Y). outputs: goal.']:
        assert phantom_paths(Program(src)) == set()


# --------------------------------------------------------- phantom projection

def test_baseline_and_wrapped_agree():
    for src in ['f(X)+=3. goal+=f(X). outputs: goal.',
                'g(w(X))+=3. goal+=g(w(X)). outputs: goal.',
                'item(d,f(X))+=3. goal+=item(d,f(X)). outputs: goal.']:
        p = Program(src)
        assert bool(phantom_paths(p))
        assert diff_ok(p, PhantomProjection(p), ['goal'])


def test_startpath3_sound():
    src = 'path(I,I). path(I,K) += path(I,J)*edge(J,K). inputs: edge(I,J). outputs: path(I,K).'
    D = 'edge(a,b)+=1. edge(b,c)+=1.'
    p = Program(src)
    assert phantom_paths(p) == set()
    assert diff_ok(p, PhantomProjection(p), ['path(a,a)', 'path(a,c)', 'path(c,c)', 'path(c,a)'], D=D)
    (PhantomProjection(p) + Program(D)).sol().assert_equal_query('path(a,a)', 1.0)


def test_diagonal_values_preserved():
    assert diff_ok(Program('q(X,X)+=2. q(X,Y)+=e(X,Y). out(A,B)+=q(A,B). inputs: e(X,Y). outputs: out(A,B).'),
                   PhantomProjection(Program('q(X,X)+=2. q(X,Y)+=e(X,Y). out(A,B)+=q(A,B). inputs: e(X,Y). outputs: out(A,B).')),
                   ['out(a,a)', 'out(c,c)', 'out(a,b)'], D='e(a,b)+=1.')


def test_constant_arg_consumed_generally_is_sound():
    p = Program('b(X,a) += 4. out(X,Y) += b(X,Y). outputs: out(X,Y).')
    assert diff_ok(p, PhantomProjection(p), ['out(a,a)', 'out(b,a)', 'out(a,b)'])


# --------------------------------------------------------------- value-split

def test_infinite_multiplicity_value_split():
    p = Program('f(1) += 2. f(X) += 3. goal += f(X). g(X) += 4*f(X). outputs: goal; g(X).')
    q = ValueSplit(p)
    assert diff_ok(p, q, ['goal', 'g(1)', 'g(7)', 'f(1)', 'f(2)'])
    q.sol().assert_equal_query('f(1)', 5.0)
    q.sol().assert_equal_query('f(2)', 3.0)
    assert is_range_restricted(q.engine_layer)


def test_multiple_specific_constants():
    p = Program('f(1) += 2. f(2) += 5. f(X) += 3. h(X) += f(X). outputs: h(X).')
    q = ValueSplit(p)
    assert diff_ok(p, q, ['h(1)', 'h(2)', 'h(7)'])
    q.sol().assert_equal_query('h(1)', 5.0)
    q.sol().assert_equal_query('h(2)', 8.0)
    q.sol().assert_equal_query('h(7)', 3.0)


def test_no_split_is_value_preserving():
    p = Program('f(X) += 3. out(X) += f(X). outputs: out(X).')
    assert diff_ok(p, ValueSplit(p), ['out(z)', 'out(a)'])


# --------------------------------------------------------------- end-to-end

def test_normalizer_value_split_then_project():
    p = Program('f(1) += 2. f(X) += 3. goal += f(X). g(X) += 4*f(X). outputs: goal; g(X).')
    q = RangeRestrictionNormalizer(p)
    assert diff_ok(p, q, ['goal', 'g(1)', 'g(7)', 'f(1)', 'f(2)'])


def test_normalizer_sound_on_startpath3():
    src = 'path(I,I). path(I,K) += path(I,J)*edge(J,K). inputs: edge(I,J). outputs: path(I,K).'
    D = 'edge(a,b)+=1. edge(b,c)+=1.'
    p = Program(src)
    assert diff_ok(p, RangeRestrictionNormalizer(p), ['path(a,a)', 'path(a,c)', 'path(c,c)'], D=D)


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
