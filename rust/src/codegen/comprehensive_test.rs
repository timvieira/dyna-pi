//! Comprehensive compiler tests from Python test suite
//!
//! This module tests the code generator against all Dyna programs
//! from the Python test suite to ensure broad coverage.

use crate::codegen::analysis::ProgramAnalysis;
use crate::codegen::generator::{CodeGenConfig, CodeGenerator};
use crate::parser::parse_program;
use std::io::Write;
use std::process::Command;

/// Test result for a single program
#[derive(Debug)]
struct TestResult {
    name: &'static str,
    parsed: bool,
    generated: bool,
    balanced_braces: bool,
    valid_syntax: bool,
    error: Option<String>,
}

/// Check that generated code is syntactically valid Rust
fn check_syntax(code: &str, test_name: &str) -> bool {
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!("dyna_comprehensive_{}.rs", test_name));

    let mut file = match std::fs::File::create(&temp_file) {
        Ok(f) => f,
        Err(_) => return false,
    };
    if writeln!(file, "{}", code).is_err() {
        return false;
    }

    let output = Command::new("rustfmt").arg(&temp_file).output();

    match output {
        Ok(result) => result.status.success(),
        Err(_) => {
            // Fallback check
            code.contains("pub struct")
                && code.contains("pub fn solve")
                && code.matches('{').count() == code.matches('}').count()
        }
    }
}

/// Run a single test program
fn test_program(name: &'static str, source: &str) -> TestResult {
    let mut result = TestResult {
        name,
        parsed: false,
        generated: false,
        balanced_braces: false,
        valid_syntax: false,
        error: None,
    };

    // Parse
    let program = match parse_program(source) {
        Ok(p) => {
            result.parsed = true;
            p
        }
        Err(e) => {
            result.error = Some(format!("Parse error: {:?}", e));
            return result;
        }
    };

    // Skip empty programs
    if program.is_empty() {
        result.error = Some("Empty program".to_string());
        return result;
    }

    // Analyze and generate
    let analysis = ProgramAnalysis::analyze(&program);
    let config = CodeGenConfig::counting();
    let generator = CodeGenerator::new(analysis, config);
    let code = generator.generate(&program);
    result.generated = true;

    // Check braces
    let open = code.matches('{').count();
    let close = code.matches('}').count();
    result.balanced_braces = open == close;

    if !result.balanced_braces {
        result.error = Some(format!("Unbalanced braces: {} open, {} close", open, close));
        return result;
    }

    // Check syntax
    result.valid_syntax = check_syntax(&code, name);
    if !result.valid_syntax {
        result.error = Some("Invalid Rust syntax".to_string());
    }

    result
}

/// Programs that should work with current code generator
/// (basic rules without lists, builtins, or special constraints)
const SUPPORTED_PROGRAMS: &[(&str, &str)] = &[
    // === Transitive Closure / Path Programs ===
    ("path_basic", r#"
        path(I, K) += edge(I, K).
        path(I, K) += path(I, J) * edge(J, K).
    "#),

    ("path_with_goal", r#"
        path(I, K) += edge(I, K).
        path(I, K) += path(I, J) * edge(J, K).
        goal += start(I) * path(I, K) * stop(K).
    "#),

    ("shortest_path", r#"
        path(I, I).
        path(I, K) += path(I, J) * edge(J, K).
        goal += start(I) * path(I, K) * stop(K).
    "#),

    // === CKY Parser ===
    ("cky_binary", r#"
        phrase(X, I, K) += rewrite(X, Y, Z) * phrase(Y, I, J) * phrase(Z, J, K).
    "#),

    ("cky_unary", r#"
        phrase(X, I, K) += rewrite(X, Y) * phrase(Y, I, K).
    "#),

    ("cky_lexical", r#"
        phrase(X, I, K) += rewrite(X, Y) * word(Y, I, K).
    "#),

    ("cky_full", r#"
        phrase(X, I, K) += rewrite(X, Y, Z) * phrase(Y, I, J) * phrase(Z, J, K).
        phrase(X, I, K) += rewrite(X, Y) * phrase(Y, I, K).
        phrase(X, I, K) += rewrite(X, Y) * word(Y, I, K).
        goal += length(N) * phrase(Root, 0, N).
    "#),

    // === Matrix Operations ===
    ("matrix_mult", r#"
        b(I, K) += a(I, J) * a(J, K).
    "#),

    ("matrix_chain", r#"
        c(I, L) += a(I, J) * b(J, K) * c(K, L).
    "#),

    // === Geometric Series ===
    ("geometric_simple", r#"
        x += 1.
        x += x.
    "#),

    ("geometric_scaled", r#"
        x(I) += 1.
        x(I) += x(I).
    "#),

    // === Catalan Numbers ===
    ("catalan", r#"
        x += 1.
        x += x * x.
    "#),

    // === Mutual Recursion ===
    ("mutual_recursion", r#"
        f += g.
        g += f.
        f += x.
        g += y.
    "#),

    ("even_odd", r#"
        even(0).
        even(N) += odd(M) * succ(M, N).
        odd(N) += even(M) * succ(M, N).
    "#),

    // === Multiple Definitions ===
    ("multi_def", r#"
        f(X, Y) += h(X, Y).
        h(I, K) += f(I, J) * g(J, K).
    "#),

    // === Chain Rules ===
    ("chain_3", r#"
        d(X) += a(X) * b(X) * c(X).
    "#),

    ("chain_4", r#"
        e(X) += a(X) * b(X) * c(X) * d(X).
    "#),

    // === Self-Join ===
    ("self_join", r#"
        goal += g(I) * g(I).
    "#),

    // === Alternating Rules ===
    ("alternating", r#"
        x += y.
        x += a * x.
    "#),

    // === Complex Goal ===
    ("complex_goal", r#"
        goal += path(J, K) * start(I) * edge(I, J1) * path(J1, J) * stop(K).
    "#),

    // === Investment/Value Propagation ===
    ("investment", r#"
        value(Person, Year) += contributed(Year) * deposit(Person).
        value(Person, Year) += value(Person, Prev) * rate(Prev, Year).
    "#),

    // === Power Iteration ===
    ("power_iter", r#"
        q(S) += p(S).
        q(S2) += p2(S2, S) * q(S).
    "#),

    // === Bilexical Dependencies ===
    ("bilexical", r#"
        rconstit(X, H, I, K) += rewrite(X, H) * word(H, I, K).
        rconstit(X, H, I, K) += rewrite3(X, H, Y, H2, Z, H3) * rconstit(Y, H2, I, J) * constit(Z, H3, J, K).
        constit(X, H, I, K) += rconstit(X, H, I, K).
        constit(X, H, I, K) += rewrite3(X, H, Y, H2, Z, H3) * constit(Y, H2, I, J) * constit(Z, H3, J, K).
        goal += constit(S, H, 0, N) * length(N).
    "#),

    // === Simple Facts ===
    ("facts_only", r#"
        edge(1, 2).
        edge(2, 3).
        edge(3, 4).
    "#),

    ("facts_matrix", r#"
        a(0, 0) += 1.
        a(0, 1) += 2.
        a(1, 0) += 3.
        a(1, 1) += 4.
    "#),

    // === Simple Fold ===
    ("fold_simple", r#"
        v(S) += start(S).
        v(S2) += v(S) * w(S, S2).
        goal += v(S) * stop(S).
    "#),

    // === Fibonacci-like ===
    ("fib_like", r#"
        f(0).
        f(Y) += f(X) * succ(X, Y).
    "#),

    // === Divisibility ===
    ("divisibility", r#"
        div2(0).
        div2(X) += div2(Y) * ss(Y, X).
        div3(0).
        div3(X) += div3(Y) * sss(Y, X).
        div6(X) += div2(X) * div3(X).
    "#),

    // === Multiple Aggregation ===
    ("multi_agg", r#"
        f(X).
        f(X) += 2.
        f(X) += 3.
        a += 2.
        a += 1.
    "#),

    // === Ternary Relations ===
    ("ternary", r#"
        r(A, B, C) += p(A, B) * q(B, C).
        s(A, C) += r(A, B, C).
    "#),

    // === 4-way Join ===
    ("four_way_join", r#"
        result(A, D) += p(A, B) * q(B, C) * r(C, D) * s(D, A).
    "#),

    // === Diamond Pattern ===
    ("diamond", r#"
        top(X) += left(X, Y) * right(X, Z) * bottom(Y, Z).
    "#),

    // === Nested Recursion ===
    ("nested_recursion", r#"
        f(X, Y) += base(X, Y).
        f(X, Z) += f(X, Y) * step(Y, Z).
        g(X, Z) += f(X, Y) * f(Y, Z).
    "#),

    // === Multiple Heads Same Functor ===
    ("multi_head", r#"
        path(X, Y) += edge(X, Y).
        path(X, Z) += path(X, Y) * edge(Y, Z).
        path(X, Z) += edge(X, Y) * path(Y, Z).
    "#),

    // === Aggregation with Constants ===
    ("agg_const", r#"
        count(0) += 1.
        count(N) += count(M) * succ(M, N).
        total += count(N).
    "#),

    // === Graph Algorithms ===
    ("reachable", r#"
        reach(X) += start(X).
        reach(Y) += reach(X) * edge(X, Y).
        goal += reach(X) * target(X).
    "#),

    ("connected", r#"
        connected(X, Y) += edge(X, Y).
        connected(X, Y) += edge(Y, X).
        connected(X, Z) += connected(X, Y) * connected(Y, Z).
    "#),

    // === Datalog-style ===
    ("ancestor", r#"
        ancestor(X, Y) += parent(X, Y).
        ancestor(X, Z) += parent(X, Y) * ancestor(Y, Z).
    "#),

    ("sibling", r#"
        sibling(X, Y) += parent(P, X) * parent(P, Y).
    "#),

    // === Weighted Paths ===
    ("weighted_path", r#"
        dist(X, X) += start(X).
        dist(X, Z) += dist(X, Y) * edge(Y, Z, W).
    "#),

    // === Hypergraph ===
    ("hyperedge", r#"
        result(A, B, C) += hyper(A, B, C, D) * node(D).
    "#),

    // === Lattice Operations ===
    ("lattice_join", r#"
        lub(X, Y, Z) += leq(X, Z) * leq(Y, Z).
    "#),
];

/// Programs that use features not yet supported
/// (for documentation and future implementation)
const UNSUPPORTED_PROGRAMS: &[(&str, &str, &str)] = &[
    // Lists
    ("beta_path", r#"
        goal += beta([X|Xs]) * start(X).
        beta([X,Y|Xs]) += beta([Y|Xs]) * edge(X,Y).
        beta([X]) += stop(X).
    "#, "List patterns not supported"),

    ("list_sum", r#"
        asum([], 0).
        asum([X|Xs], S) :- asum(Xs, S2), S is S2 + X.
    "#, "Lists and 'is' builtin not supported"),

    // Builtins
    ("arithmetic", r#"
        f(X, Y) += X is 2 + 4, Y is X + 1.
    "#, "'is' builtin not supported"),

    ("comparison", r#"
        goal(A, B, C) += (A < B), (B < C).
    "#, "Comparison builtins not supported"),

    ("chained_compare", r#"
        goal += 0 <= X <= Y < 3.
    "#, "Chained comparison not supported"),

    // Unification
    ("unification", r#"
        f(X, Y) += (X = Y) * 2.
    "#, "Explicit unification not supported"),

    // Negation/Special
    ("negation", r#"
        goal += $not_matches(f(X), f(3)).
    "#, "Negation/special predicates not supported"),

    ("free_bound", r#"
        f(X) := $free(X).
        f(Y) += $bound(Y).
    "#, "$free/$bound not supported"),

    // Type constraints
    ("type_fail", r#"
        $fail :- k(X), n(X).
    "#, "$fail and type constraints not supported"),
];

#[test]
fn test_all_supported_programs() {
    println!("\n============================================================");
    println!("COMPREHENSIVE CODE GENERATOR TEST");
    println!("============================================================\n");

    let mut passed = 0;
    let mut failed = 0;
    let mut results: Vec<TestResult> = Vec::new();

    for (name, source) in SUPPORTED_PROGRAMS {
        let result = test_program(name, source);

        let status = if result.valid_syntax {
            passed += 1;
            "✓ PASS"
        } else {
            failed += 1;
            "✗ FAIL"
        };

        println!("{}: {} {}",
            name,
            status,
            result.error.as_deref().unwrap_or("")
        );

        results.push(result);
    }

    println!("\n------------------------------------------------------------");
    println!("SUMMARY: {} passed, {} failed out of {} programs",
        passed, failed, SUPPORTED_PROGRAMS.len());
    println!("------------------------------------------------------------\n");

    // Print details of failures
    let failures: Vec<_> = results.iter().filter(|r| !r.valid_syntax).collect();
    if !failures.is_empty() {
        println!("FAILURES:");
        for f in &failures {
            println!("  - {}: {:?}", f.name, f.error);
        }
        println!();
    }

    assert_eq!(failed, 0, "{} programs failed code generation", failed);
}

#[test]
fn test_document_unsupported() {
    println!("\n============================================================");
    println!("UNSUPPORTED PROGRAMS (for future implementation)");
    println!("============================================================\n");

    for (name, _source, reason) in UNSUPPORTED_PROGRAMS {
        println!("{}: {}", name, reason);
    }

    println!("\nTotal unsupported: {}", UNSUPPORTED_PROGRAMS.len());
}

/// Test that we can at least parse all programs
#[test]
fn test_parse_all() {
    let mut parse_failures = 0;

    for (name, source) in SUPPORTED_PROGRAMS {
        if parse_program(source).is_err() {
            println!("Parse failed: {}", name);
            parse_failures += 1;
        }
    }

    assert_eq!(parse_failures, 0, "{} programs failed to parse", parse_failures);
}

/// Test specific program and print generated code
#[test]
fn test_print_generated_code() {
    let programs_to_print = ["cky_full", "path_with_goal", "bilexical"];

    for name in programs_to_print {
        if let Some((_, source)) = SUPPORTED_PROGRAMS.iter().find(|(n, _)| *n == name) {
            let program = parse_program(source).expect("Failed to parse");
            let analysis = ProgramAnalysis::analyze(&program);
            let config = CodeGenConfig::counting();
            let generator = CodeGenerator::new(analysis, config);
            let code = generator.generate(&program);

            println!("\n============================================================");
            println!("Generated code for: {}", name);
            println!("============================================================");
            println!("{}", code);
        }
    }
}
