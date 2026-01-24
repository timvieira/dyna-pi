"""Tests for the dyna-rust Python bindings."""

import pytest


def test_import():
    """Test that the module can be imported."""
    import dyna_rust
    assert hasattr(dyna_rust, 'Term')
    assert hasattr(dyna_rust, 'Solver')


def test_term_creation():
    """Test creating terms."""
    import dyna_rust

    # Create a compound term
    t = dyna_rust.Term("f", 1, 2)
    assert t.functor == "f"
    assert t.arity == 2
    assert t.is_ground()

    # Create a variable
    v = dyna_rust.Term.var(0)
    assert v.is_var()
    assert not v.is_ground()

    # Create an atom
    a = dyna_rust.Term.atom("foo")
    assert a.functor == "foo"
    assert a.arity == 0


def test_term_nested():
    """Test creating nested terms."""
    import dyna_rust

    inner = dyna_rust.Term("g", 1)
    outer = dyna_rust.Term("f", inner, 2)

    assert outer.functor == "f"
    assert outer.arity == 2


def test_unification():
    """Test unification."""
    import dyna_rust

    # Unify variable with constant
    x = dyna_rust.Term.var(0)
    c = dyna_rust.Term.int(42)

    subst = dyna_rust.py_unify(x, c)
    assert subst is not None

    result = subst.apply(x)
    assert str(result) == "42"


def test_unification_compound():
    """Test unification of compound terms."""
    import dyna_rust

    t1 = dyna_rust.Term("f", dyna_rust.Term.var(0), 1)
    t2 = dyna_rust.Term("f", 2, dyna_rust.Term.var(1))

    subst = dyna_rust.py_unify(t1, t2)
    assert subst is not None
    assert len(subst) == 2


def test_unification_failure():
    """Test unification failure."""
    import dyna_rust

    t1 = dyna_rust.Term("f", 1)
    t2 = dyna_rust.Term("g", 1)

    subst = dyna_rust.py_unify(t1, t2)
    assert subst is None


def test_covers():
    """Test one-way matching."""
    import dyna_rust

    pattern = dyna_rust.Term("f", dyna_rust.Term.var(0), dyna_rust.Term.var(1))
    term = dyna_rust.Term("f", 1, 2)

    subst = dyna_rust.py_covers(pattern, term)
    assert subst is not None


def test_canonicalize():
    """Test term canonicalization."""
    import dyna_rust

    # f(Y, X, Y) with arbitrary variable IDs
    t = dyna_rust.Term("f",
        dyna_rust.Term.var(5),
        dyna_rust.Term.var(3),
        dyna_rust.Term.var(5))

    canon = dyna_rust.canonicalize(t)
    # Should become f(_0, _1, _0)
    assert "_0" in str(canon)
    assert "_1" in str(canon)


def test_alpha_equivalent():
    """Test alpha equivalence."""
    import dyna_rust

    t1 = dyna_rust.Term("f", dyna_rust.Term.var(0), dyna_rust.Term.var(1))
    t2 = dyna_rust.Term("f", dyna_rust.Term.var(5), dyna_rust.Term.var(10))

    assert dyna_rust.alpha_equivalent(t1, t2)


def test_rule_creation():
    """Test creating rules."""
    import dyna_rust

    head = dyna_rust.Term("goal", dyna_rust.Term.var(0))
    body = [
        dyna_rust.Term("f", dyna_rust.Term.var(0), dyna_rust.Term.var(1)),
        dyna_rust.Term("g", dyna_rust.Term.var(1)),
    ]

    rule = dyna_rust.Rule(head, body)
    assert not rule.is_fact()
    assert len(rule.body()) == 2


def test_rule_fact():
    """Test creating facts."""
    import dyna_rust

    fact = dyna_rust.Rule.fact(dyna_rust.Term("base", 0))
    assert fact.is_fact()


def test_solver_facts():
    """Test solver with just facts."""
    import dyna_rust

    rules = [
        dyna_rust.Rule.fact(dyna_rust.Term("edge", 1, 2)),
        dyna_rust.Rule.fact(dyna_rust.Term("edge", 2, 3)),
    ]

    solver = dyna_rust.Solver(rules)
    solver.solve()

    assert solver.chart_size() == 2
    assert solver.lookup(dyna_rust.Term("edge", 1, 2)) == 1.0
    assert solver.lookup(dyna_rust.Term("edge", 1, 3)) is None


def test_solver_transitive():
    """Test solver with transitive closure."""
    import dyna_rust

    # path(X, Y) += edge(X, Y)
    # path(X, Z) += edge(X, Y) * path(Y, Z)
    rules = [
        dyna_rust.Rule(
            dyna_rust.Term("path", dyna_rust.Term.var(0), dyna_rust.Term.var(1)),
            [dyna_rust.Term("edge", dyna_rust.Term.var(0), dyna_rust.Term.var(1))]
        ),
        dyna_rust.Rule(
            dyna_rust.Term("path", dyna_rust.Term.var(0), dyna_rust.Term.var(2)),
            [
                dyna_rust.Term("edge", dyna_rust.Term.var(0), dyna_rust.Term.var(1)),
                dyna_rust.Term("path", dyna_rust.Term.var(1), dyna_rust.Term.var(2)),
            ]
        ),
    ]

    solver = dyna_rust.Solver(rules)
    solver.update(dyna_rust.Term("edge", 1, 2), 1.0)
    solver.update(dyna_rust.Term("edge", 2, 3), 1.0)
    solver.update(dyna_rust.Term("edge", 3, 4), 1.0)
    solver.solve()

    # Check transitive paths
    assert solver.lookup(dyna_rust.Term("path", 1, 2)) is not None
    assert solver.lookup(dyna_rust.Term("path", 1, 3)) is not None
    assert solver.lookup(dyna_rust.Term("path", 1, 4)) is not None


def test_solver_query():
    """Test solver query."""
    import dyna_rust

    solver = dyna_rust.Solver([])
    solver.update(dyna_rust.Term("edge", 1, 2), 1.0)
    solver.update(dyna_rust.Term("edge", 1, 3), 2.0)
    solver.update(dyna_rust.Term("edge", 2, 3), 3.0)
    solver.solve()

    # Query for all edges from node 1
    pattern = dyna_rust.Term("edge", 1, dyna_rust.Term.var(0))
    results = solver.query(pattern)

    assert len(results) == 2


def test_solver_stats():
    """Test solver statistics."""
    import dyna_rust

    solver = dyna_rust.Solver([
        dyna_rust.Rule.fact(dyna_rust.Term("f", 1)),
    ])
    solver.solve()

    stats = solver.stats()
    assert 'iterations' in stats
    assert 'chart_size' in stats


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
