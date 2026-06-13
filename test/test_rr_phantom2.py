"""
Tests for the path-based phantom normalization (dyna/transform/rr_phantom2.py)
— the range-restriction projection that is *both* provably sound *and* invariant
under superficial structure changes (wrapping in a dummy functor / distraction
argument).

The flat phantom analysis (rr_phantom.py) is sound but not invariant: wrapping a
phantom variable defeats it.  This keys phantom-ness on tree *paths*, so:

  - wrapped phantoms are still found and projected (invariance), and
  - single-occurrence still excludes diagonals (soundness, e.g. startpath3).
"""

from dyna import Program
from dyna.transform.rr_phantom2 import phantom_paths, RangeRestrictionPhantomPath
from dyna.analyze.range_restriction import is_range_restricted


def diff_ok(src, D, queries):
    p = Program(src)
    q = RangeRestrictionPhantomPath(p)
    ps, qs = (p + Program(D)).sol(), (q + Program(D)).sol()
    return all([str(x) for x in ps.user_query(qy)] == [str(x) for x in qs.user_query(qy)]
               for qy in queries)


def projected(src):
    return bool(phantom_paths(Program(src)))


# ---------------------------------------------------------------- invariance

def test_wrapping_does_not_hide_the_phantom():
    # the phantom is found at depth, under a wrapper or a distraction argument
    assert phantom_paths(Program('f(X) += 3. goal += f(X). outputs: goal.')) == {('f', 1, (0,))}
    assert phantom_paths(Program('g(w(X)) += 3. goal += g(w(X)). outputs: goal.')) == {('g', 1, (0, 0))}
    assert phantom_paths(Program(
        'item(d,f(X)) += 3. goal += item(d,f(X)). outputs: goal.')) == {('item', 2, (1, 0))}


def test_baseline_and_wrapped_agree():
    # both the bare and the wrapped program normalize AND give identical values
    assert projected('f(X)+=3. goal+=f(X). outputs: goal.')
    assert projected('g(w(X))+=3. goal+=g(w(X)). outputs: goal.')
    assert diff_ok('f(X)+=3. goal+=f(X). outputs: goal.', '', ['goal'])
    assert diff_ok('g(w(X))+=3. goal+=g(w(X)). outputs: goal.', '', ['goal'])
    assert diff_ok('item(d,f(X))+=3. goal+=item(d,f(X)). outputs: goal.', '', ['goal'])


def test_wrapped_propagation_chain():
    src = 'a(w(X))+=3. b(w(X))+=a(w(X)). out(w(X))+=b(w(X)). outputs: out(W).'
    assert projected(src)
    assert diff_ok(src, '', ['out(w(z))', 'out(w(a))'])


# ----------------------------------------------------------------- soundness

def test_startpath3_refused_and_sound():
    # the diagonal is never projected (single-occurrence excludes it); values
    # exact (the abbreviate+usefulness path computes all-zeros here)
    src = 'path(I,I). path(I,K) += path(I,J)*edge(J,K). inputs: edge(I,J). outputs: path(I,K).'
    assert not projected(src)
    D = 'edge(a,b)+=1. edge(b,c)+=1.'
    assert diff_ok(src, D, ['path(a,a)', 'path(a,c)', 'path(c,c)', 'path(c,a)'])
    # concretely: the diagonal is non-zero (the abbreviate bug was all-zeros)
    (RangeRestrictionPhantomPath(Program(src)) + Program(D)).sol().assert_equal_query('path(a,a)', 1.0)


def test_diagonals_refused():
    for src in ['q(X,X)+=2. q(X,Y)+=e(X,Y). out(A,B)+=q(A,B). inputs: e(X,Y). outputs: out(A,B).',
                'temp(pair(X0,X0))+=1. temp(pair(X,X0))+=rewrite(X,Y)*temp(pair(Y,X0)). inputs: rewrite(X,Y). outputs: temp(W).']:
        assert not projected(src)


def test_diagonal_values_preserved():
    assert diff_ok('q(X,X)+=2. q(X,Y)+=e(X,Y). out(A,B)+=q(A,B). inputs: e(X,Y). outputs: out(A,B).',
                   'e(a,b)+=1.', ['out(a,a)', 'out(c,c)', 'out(a,b)'])


def test_constant_arg_consumed_generally_is_sound():
    # the bug the wrapped fuzz found: b defined with a constant arg, consumed at
    # a general position, must NOT spuriously project out's position (-> inf)
    src = 'b(X,a) += 4. out(X,Y) += b(X,Y). outputs: out(X,Y).'
    assert diff_ok(src, '', ['out(a,a)', 'out(b,a)', 'out(a,b)'])


def test_engine_layer_range_restricted():
    q = RangeRestrictionPhantomPath(Program('g(w(X))+=3. out(w(X))+=g(w(X)). outputs: out(W).'))
    assert is_range_restricted(q.engine_layer)


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
