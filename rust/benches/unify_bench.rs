//! Benchmarks for unification operations.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use dyna_rust::{Subst, Term, Value};

fn create_deep_term(depth: usize) -> Term {
    if depth == 0 {
        Term::var(0)
    } else {
        Term::compound("f", vec![create_deep_term(depth - 1)])
    }
}

fn bench_unify_simple(c: &mut Criterion) {
    let x = Term::var(0);
    let y = Term::constant(Value::Int(42));

    c.bench_function("unify_var_const", |b| {
        b.iter(|| {
            let mut subst = Subst::new();
            subst.mgu(black_box(&x), black_box(&y)).unwrap();
        })
    });
}

fn bench_unify_compound(c: &mut Criterion) {
    let t1 = Term::compound(
        "f",
        vec![Term::var(0), Term::var(1), Term::constant(Value::Int(1))],
    );
    let t2 = Term::compound(
        "f",
        vec![
            Term::constant(Value::Int(2)),
            Term::constant(Value::Int(3)),
            Term::var(2),
        ],
    );

    c.bench_function("unify_compound_3", |b| {
        b.iter(|| {
            let mut subst = Subst::new();
            subst.mgu(black_box(&t1), black_box(&t2)).unwrap();
        })
    });
}

fn bench_unify_deep(c: &mut Criterion) {
    let t1 = create_deep_term(10);
    let t2 = create_deep_term(10);

    c.bench_function("unify_deep_10", |b| {
        b.iter(|| {
            let mut subst = Subst::new();
            let _ = subst.mgu(black_box(&t1), black_box(&t2));
        })
    });
}

fn bench_deref(c: &mut Criterion) {
    let mut subst = Subst::new();
    for i in 0..10 {
        subst.bind(i, Term::var(i + 1));
    }
    subst.bind(10, Term::constant(Value::Int(42)));

    let x = Term::var(0);

    c.bench_function("deref_chain_10", |b| {
        b.iter(|| subst.deref(black_box(&x)))
    });
}

fn bench_fresh(c: &mut Criterion) {
    let term = Term::compound(
        "f",
        vec![
            Term::var(0),
            Term::compound("g", vec![Term::var(1), Term::var(0)]),
            Term::var(2),
        ],
    );

    c.bench_function("fresh_compound", |b| {
        b.iter(|| {
            let mut subst = Subst::with_next_var(100);
            subst.fresh(black_box(&term))
        })
    });
}

fn bench_canonicalize(c: &mut Criterion) {
    let term = Term::compound(
        "f",
        vec![
            Term::var(5),
            Term::compound("g", vec![Term::var(10), Term::var(5)]),
            Term::var(15),
        ],
    );

    c.bench_function("canonicalize", |b| {
        b.iter(|| Subst::canonicalize(black_box(&term)))
    });
}

criterion_group!(
    benches,
    bench_unify_simple,
    bench_unify_compound,
    bench_unify_deep,
    bench_deref,
    bench_fresh,
    bench_canonicalize,
);
criterion_main!(benches);
