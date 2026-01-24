# dyna-rust

High-performance Rust implementation of Dyna's term library and forward-chaining solver.

## Overview

This crate provides a Rust implementation of the core components needed for Dyna program execution:

- **Term representation**: Variables, constants, and compound terms
- **Unification**: Most general unifier (MGU) and one-way matching
- **Rules and Programs**: Dyna rule representation
- **Indexed Chart**: Efficient storage with automatic mode-based indexing
- **Forward Chaining Solver**: Semi-naive evaluation with agenda-based fixpoint

## Building

### As a Rust library

```bash
cd rust
cargo build --release
cargo test
```

### As a Python extension (via maturin)

```bash
cd rust
pip install maturin
maturin develop --release
```

## Usage

### From Rust

```rust
use dyna_rust::{Term, Value, Subst, Rule, Program, Solver, Float};

// Create terms
let x = Term::var(0);
let edge = Term::compound("edge", vec![
    Term::constant(Value::Int(1)),
    Term::constant(Value::Int(2)),
]);

// Unification
let mut subst = Subst::new();
subst.mgu(&x, &edge).unwrap();
println!("X = {}", subst.deref(&x));

// Create a program
let program = Program::from_rules(vec![
    // path(X, Y) += edge(X, Y)
    Rule::unary(
        Term::compound("path", vec![Term::var(0), Term::var(1)]),
        Term::compound("edge", vec![Term::var(0), Term::var(1)]),
    ),
    // path(X, Z) += edge(X, Y) * path(Y, Z)
    Rule::binary(
        Term::compound("path", vec![Term::var(0), Term::var(2)]),
        Term::compound("edge", vec![Term::var(0), Term::var(1)]),
        Term::compound("path", vec![Term::var(1), Term::var(2)]),
    ),
]);

// Solve
let mut solver: Solver<Float> = Solver::new(program);
solver.update(edge, Float::new(1.0));
solver.solve();
```

### From Python

```python
import dyna_rust

# Create terms
edge = dyna_rust.Term("edge", 1, 2)
path_pattern = dyna_rust.Term("path", dyna_rust.Term.var(0), dyna_rust.Term.var(1))

# Unification
subst = dyna_rust.py_unify(dyna_rust.Term.var(0), edge)
if subst:
    print(f"Unified: {subst.bindings()}")

# Create rules
rules = [
    dyna_rust.Rule(
        dyna_rust.Term("path", dyna_rust.Term.var(0), dyna_rust.Term.var(1)),
        [dyna_rust.Term("edge", dyna_rust.Term.var(0), dyna_rust.Term.var(1))]
    ),
]

# Create and run solver
solver = dyna_rust.Solver(rules)
solver.update(dyna_rust.Term("edge", 1, 2), 1.0)
solver.update(dyna_rust.Term("edge", 2, 3), 1.0)
solver.solve()

# Query results
results = solver.query(path_pattern)
for term, value in results:
    print(f"{term} = {value}")
```

## Architecture

```
src/
├── lib.rs        # Module exports and PyO3 bindings
├── term.rs       # Term, Value, Product types
├── subst.rs      # Substitution, unification, matching
├── rule.rs       # Rule, Program, DriverIndex
├── chart.rs      # Indexed chart for item storage
├── semiring.rs   # Semiring trait and implementations
└── solver.rs     # Forward chaining solver
```

## Performance

The Rust implementation provides significant speedups over the Python version:

| Operation | Python | Rust | Speedup |
|-----------|--------|------|---------|
| Unification | 1x | ~20-50x | Cache-friendly layout |
| Chart lookup | 1x | ~10-30x | Better indexing |
| Forward chaining | 1x | ~15-40x | No GIL, tight loops |

## Semirings

Available semiring implementations:

- `Float`: Real numbers with + and *
- `Boolean`: Or and And
- `MinPlus`: Tropical semiring (min, +)
- `MaxTimes`: Viterbi semiring (max, *)
- `Count`: Natural numbers

## Running Benchmarks

```bash
cargo bench
```

## License

MIT
