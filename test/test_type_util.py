from dyna import term, same, covers, canonicalize
from arsenal import assert_throws
from dyna import NoDupsSet, MostGeneralSet, DisjointEstimate


def test_no_dups():

    xs = NoDupsSet([], same)
    assert len(xs) == 0

    xs.add(term('f(3,4)'))
    assert len(xs) == 1, len(xs)
    with assert_throws(KeyError):
        xs.find(term('f(g(X),h(Y))'))

    with assert_throws(KeyError):
        xs.root(term('f(X,Y)'))

    xs.add(term('f(3,Y)'))
    assert len(xs) == 2
    assert same(xs.root(term('f(3,4)')), term('f(3,4)'))
    with assert_throws(KeyError):
        xs.root(term('f(X,Y)'))

    xs.add(term('f(X,Y)'))
    assert len(xs) == 3
    assert same(xs.root(term('f(X,Y)')), term('f(X,Y)'))
    assert same(xs.root(term('f(3,Y)')), term('f(3,Y)'))
    with assert_throws(KeyError):
        xs.root(term('f(4,Y)'))


def test_most_general():

    xs = MostGeneralSet([], covers)

    xs.add(term('f(3,4)'))
    with assert_throws(KeyError):
        xs.find(term('f(g(X),h(Y))'))

    with assert_throws(KeyError):
        xs.root(term('f(X,Y)'))

    xs.add(term('f(3,Y)'))
    assert len(xs) == 1
    assert xs.root(term('f(3,4)')) == xs.root(term('f(3,Y)'))
    with assert_throws(KeyError):
        xs.root(term('f(X,Y)'))

    xs.add(term('f(X,Y)'))
    assert xs.root(term('f(X,Y)')) == xs.root(term('f(3,4)'))
    assert xs.root(term('f(3,Y)')) == xs.root(term('f(3,4)'))

    assert len(xs) == 1


def test_disjoint():

    xs = DisjointEstimate()

    xs.add(term('f(3,4)'))
    with assert_throws(KeyError):
        xs.find(term('f(g(X),h(Y))'))

    xs.add(term('f(3,Y)'))

    assert same(xs.xs[0], term('f(3,Y)'))
    assert len(xs) == 1

    xs.add(term('f(X,4)'))

    assert len(xs) == 1
    assert same(xs.xs[0], term('f(X,Y)'))

    xs.add(term('g(X,h(X,X))'))
    xs.add(term('g(X,h(X,Y))'))
    assert same(xs.xs[1], term('g(X,h(X,Y))'))

    assert xs.find(term('f(3,4)')) == 0
    assert xs.find(term('f(X,11)')) == 0
    assert xs.find(term('f(X,Y)')) == 0

    assert same(xs.root(term('f(1,2)')), term('f(X,Y)'))
    assert same(xs.root(term('f(X,Y)')), term('f(X,Y)'))

    with assert_throws(KeyError):
        assert xs.find(term('X'))

    assert xs.find(term('f(g(X),h(Y))')) == 0

    with assert_throws(KeyError):
        xs.find(term('goal'))


def test_disjoint_var_capture():
    # Regression: overlapping patterns must MERGE even when a structured position lines up with a
    # variable that (because stored entries are canonical) shares the interned name `$X..`.  `unifies`
    # compares vars by identity, so without renaming apart this trips a spurious occurs-check
    # (`st($X0,0)` vs `$X0`); the generalizer ALSO re-injects a matched entry's vars, re-polluting the
    # working term.  Both left overlapping entries unmerged -> `find` raised "not a unique type"
    # (surfaced while magic-solving a Defun+span program).
    xs = DisjointEstimate()
    xs.add(term('h(st(W,0), B, st(H,1), D)'))   # structured: pos0 st(_,0), pos2 st(_,1)
    xs.add(term('h(A,B,A,B)'))                  # diagonal -- genuinely disjoint from it (0 != 1)
    xs.add(term('h(st(S,0), B, C, D)'))         # generalizes the diagonal -> generic, which must then
    assert len(xs) == 1, list(xs)               # absorb the structured entry (the merge the bug broke)
    assert same(xs.xs[0], term('h(A,B,C,D)'))
    # a doubly-structured query resolves to the single (generic) type, not "not a unique type"
    assert same(xs.root(term('h(st(W,0), G, st(H,1), G2)')), term('h(A,B,C,D)'))


def test_most_general_var_capture():
    # Regression: `covers` is a SET relation, so MostGeneralSet must compare entries with variables
    # taken independently.  With entries sharing interned canonical names ($X0...), a structured
    # position vs a same-named var made `covers(generic, structured)` spuriously False, so the generic
    # failed to subsume/evict the structured entry (the antichain kept both).
    A = canonicalize(term('h(st(X0,0),X1,st(X2,1),X3)'))   # structured
    B = canonicalize(term('h(X0,X1,X2,X3)'))               # generic -- covers A
    for order in ([A, B], [B, A]):
        mg = MostGeneralSet([], covers)
        for x in order:
            mg.add(x)
        assert len(mg) == 1, [str(x) for x in mg]
        assert same(mg.xs[0], term('h(W,X,Y,Z)'))


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
