//! Benchmark comparing compiled CKY parser vs generic solver
//!
//! Run with: cargo bench --bench cky_compiled_bench
//!
//! This benchmark demonstrates the performance advantage of specialized,
//! compiled code generation over the generic solver.

use std::time::Instant;

use dyna_rust::codegen::cky_compiled::create_parser;
use dyna_rust::rule::{Program, Rule};
use dyna_rust::semiring::Float;
use dyna_rust::solver::Solver;
use dyna_rust::term::{Product, Term, Value};

/// Build a CKY grammar for benchmarking.
/// Grammar with PP attachment ambiguity:
///   S -> NP VP
///   NP -> Det N
///   NP -> NP PP
///   VP -> V NP
///   VP -> VP PP
///   PP -> P NP
fn build_generic_solver(n: usize) -> (Solver<Float>, Vec<String>) {
    // Rules for CKY parsing
    let rules = vec![
        // phrase(X, I, K) += phrase(Y, I, J) * phrase(Z, J, K) * rewrite(X, Y, Z).
        Rule::new(
            Term::compound("phrase", vec![Term::var(0), Term::var(3), Term::var(5)]),
            Product::new(vec![
                Term::compound("phrase", vec![Term::var(1), Term::var(3), Term::var(4)]),
                Term::compound("phrase", vec![Term::var(2), Term::var(4), Term::var(5)]),
                Term::compound("rewrite", vec![Term::var(0), Term::var(1), Term::var(2)]),
            ]),
        ),
    ];

    let program = Program::from_rules(rules);
    let mut solver = Solver::new(program);

    // Add grammar rules
    solver.update(
        Term::compound("rewrite", vec![Term::atom("S"), Term::atom("NP"), Term::atom("VP")]),
        Float::new(1.0),
    );
    solver.update(
        Term::compound("rewrite", vec![Term::atom("NP"), Term::atom("Det"), Term::atom("N")]),
        Float::new(1.0),
    );
    solver.update(
        Term::compound("rewrite", vec![Term::atom("NP"), Term::atom("NP"), Term::atom("PP")]),
        Float::new(1.0),
    );
    solver.update(
        Term::compound("rewrite", vec![Term::atom("VP"), Term::atom("V"), Term::atom("NP")]),
        Float::new(1.0),
    );
    solver.update(
        Term::compound("rewrite", vec![Term::atom("VP"), Term::atom("VP"), Term::atom("PP")]),
        Float::new(1.0),
    );
    solver.update(
        Term::compound("rewrite", vec![Term::atom("PP"), Term::atom("P"), Term::atom("NP")]),
        Float::new(1.0),
    );

    // Generate sentence: "the man saw the man with the telescope with the telescope ..."
    let mut words = vec!["the", "man", "saw"];
    let num_pps = (n - 3) / 3;
    for _ in 0..num_pps {
        words.push("with");
        words.push("the");
        words.push("telescope");
    }
    // Pad with extra words if needed
    while words.len() < n {
        words.push("the");
    }
    words.truncate(n);

    // Add lexical items
    for (i, word) in words.iter().enumerate() {
        let cat = match *word {
            "the" => "Det",
            "man" | "telescope" => "N",
            "saw" => "V",
            "with" => "P",
            _ => "N",
        };
        solver.update(
            Term::compound(
                "phrase",
                vec![
                    Term::atom(cat),
                    Term::constant(Value::Int(i as i64)),
                    Term::constant(Value::Int((i + 1) as i64)),
                ],
            ),
            Float::new(1.0),
        );
    }

    (solver, words.iter().map(|s| s.to_string()).collect())
}

fn build_compiled_parser() -> dyna_rust::codegen::cky_compiled::CompiledCKY {
    let grammar = vec![
        ("S", "NP", "VP"),
        ("NP", "Det", "N"),
        ("NP", "NP", "PP"),
        ("VP", "V", "NP"),
        ("VP", "VP", "PP"),
        ("PP", "P", "NP"),
    ];

    let lexicon = vec![
        ("Det", "the"),
        ("N", "man"),
        ("N", "telescope"),
        ("V", "saw"),
        ("P", "with"),
    ];

    create_parser(&grammar, &lexicon, "S")
}

fn generate_sentence(n: usize) -> Vec<&'static str> {
    let mut words: Vec<&'static str> = vec!["the", "man", "saw"];
    let num_pps = (n - 3) / 3;
    for _ in 0..num_pps {
        words.push("with");
        words.push("the");
        words.push("telescope");
    }
    // Ensure we have exactly n words
    while words.len() < n {
        words.push("the");
    }
    words.truncate(n);
    words
}

fn bench_generic_solver(n: usize, iterations: usize) -> f64 {
    let mut total_time = 0.0;

    for _ in 0..iterations {
        let (mut solver, _words) = build_generic_solver(n);
        let start = Instant::now();
        solver.solve();
        total_time += start.elapsed().as_secs_f64();
    }

    total_time / iterations as f64
}

fn bench_compiled_parser(n: usize, iterations: usize) -> f64 {
    let parser = build_compiled_parser();
    let sentence = generate_sentence(n);
    let sentence_refs: Vec<&str> = sentence.iter().map(|s| *s).collect();

    let mut total_time = 0.0;

    for _ in 0..iterations {
        let start = Instant::now();
        let _ = parser.parse(&sentence_refs);
        total_time += start.elapsed().as_secs_f64();
    }

    total_time / iterations as f64
}

fn main() {
    println!("=======================================================================");
    println!("Compiled CKY Parser vs Generic Solver Benchmark");
    println!("=======================================================================\n");

    // Test different sentence lengths
    let test_cases = [
        (5, 1000),   // 5 words, 1000 iterations
        (8, 500),    // 8 words (1 PP)
        (11, 200),   // 11 words (2 PPs)
        (14, 100),   // 14 words (3 PPs)
        (17, 50),    // 17 words (4 PPs)
        (20, 20),    // 20 words (5 PPs)
    ];

    println!("{:>8} {:>15} {:>15} {:>12}", "Length", "Generic (ms)", "Compiled (ms)", "Speedup");
    println!("{:-<8} {:-<15} {:-<15} {:-<12}", "", "", "", "");

    for (n, iterations) in test_cases {
        let generic_time = bench_generic_solver(n, iterations);
        let compiled_time = bench_compiled_parser(n, iterations);
        let speedup = generic_time / compiled_time;

        println!(
            "{:>8} {:>15.4} {:>15.4} {:>11.1}x",
            n,
            generic_time * 1000.0,
            compiled_time * 1000.0,
            speedup
        );
    }

    println!("\n=======================================================================");
    println!("Summary: Code generation provides significant speedups through:");
    println!("  - Specialized 6-byte Phrase struct (vs ~48-byte generic Term)");
    println!("  - Array-based index lookups (vs hash table lookups)");
    println!("  - No unification overhead (direct field access)");
    println!("  - No substitution tables");
    println!("  - Inlined semiring operations");
    println!("=======================================================================");
}
