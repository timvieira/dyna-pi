from dyna import term, same, covers
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


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
