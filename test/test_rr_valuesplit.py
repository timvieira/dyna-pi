"""
Tests for the value-split (disjoint case-splitting) transform
(dyna/transform/rr_valuesplit.py).

Closes the constant/variable overlap gap (`f(1)`/`f(X)`) with a sound
default+exception decomposition: f = f_default (general/phantom part, projected)
+ f_spec (specific deltas).  Sound by linearity of the semiring `+` over the
rule partition — no disequality guards, no merge heuristic.
"""

from dyna import Program
from dyna.transform.rr_valuesplit import ValueSplit
from dyna.transform.rr_phantom2 import RangeRestrictionPhantomPath
from dyna.analyze.range_restriction import is_range_restricted


def diff_ok(p, q, queries, D=''):
    ps, qs = (p + Program(D)).sol(), (q + Program(D)).sol()
    return all([str(x) for x in ps.user_query(qy)] == [str(x) for x in qs.user_query(qy)]
               for qy in queries)


def test_infinite_multiplicity_value_split():
    # the canonical value-split, now sound: f(1)/f(X) overlap
    p = Program('f(1) += 2. f(X) += 3. goal += f(X). g(X) += 4*f(X). outputs: goal; g(X).')
    q = ValueSplit(p)
    assert diff_ok(p, q, ['goal', 'g(1)', 'g(7)', 'f(1)', 'f(2)'])
    # f(1)=5 (2 specific + 3 default), f(2)=3 (default only)
    (q).sol().assert_equal_query('f(1)', 5.0)
    (q).sol().assert_equal_query('f(2)', 3.0)
    # the residue is only the recovery-form "default" rules
    for r in q.residual_layer.rules:
        body = [b for b in r.body if not q.is_const(b)]
        assert any('_dft' in str(b) for b in body)


def test_multiple_specific_constants():
    # f(1)/f(2)/f(X): default applies to all, specifics add
    p = Program('f(1) += 2. f(2) += 5. f(X) += 3. h(X) += f(X). outputs: h(X).')
    q = ValueSplit(p)
    assert diff_ok(p, q, ['h(1)', 'h(2)', 'h(7)'])
    q.sol().assert_equal_query('h(1)', 5.0)   # 3 + 2
    q.sol().assert_equal_query('h(2)', 8.0)   # 3 + 5
    q.sol().assert_equal_query('h(7)', 3.0)   # 3


def test_two_arg_partial_overlap():
    p = Program('f(a, Y) += 2. f(X, Y) += 3. out(X,Y) += f(X,Y). inputs: dummy(Z). outputs: out(X,Y).')
    q = ValueSplit(p)
    assert diff_ok(p, q, ['out(a,a)', 'out(a,b)', 'out(b,b)'], D='dummy(z) += 1.')


def test_no_split_is_value_preserving():
    # a program with no overlap is left value-equivalent
    p = Program('f(X) += 3. out(X) += f(X). outputs: out(X).')
    q = ValueSplit(p)
    assert diff_ok(p, q, ['out(z)', 'out(a)'])


def test_engine_layer_range_restricted():
    p = Program('f(1) += 2. f(X) += 3. goal += f(X). g(X) += 4*f(X). outputs: goal; g(X).')
    q = ValueSplit(p)
    assert is_range_restricted(q.engine_layer)


def test_composes_with_phantom_path():
    p = Program('f(1) += 2. f(X) += 3. goal += f(X). g(X) += 4*f(X). outputs: goal; g(X).')
    q = RangeRestrictionPhantomPath(ValueSplit(p))
    assert diff_ok(p, q, ['goal', 'g(1)', 'g(7)', 'f(1)', 'f(2)'])


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
