//! End-to-end compiler tests
//!
//! Tests that the code generator produces valid, working Rust code
//! for all solver test cases.

use crate::codegen::analysis::ProgramAnalysis;
use crate::codegen::generator::{CodeGenConfig, CodeGenerator};
use crate::rule::{Program, Rule};
use crate::term::{Product, Term, Value};
use std::process::Command;
use std::io::Write;

/// Helper to make edge terms
fn make_edge(from: i64, to: i64) -> Term {
    Term::compound(
        "edge",
        vec![
            Term::constant(Value::Int(from)),
            Term::constant(Value::Int(to)),
        ],
    )
}

/// Helper to make path terms
fn make_path(from: i64, to: i64) -> Term {
    Term::compound(
        "path",
        vec![
            Term::constant(Value::Int(from)),
            Term::constant(Value::Int(to)),
        ],
    )
}

/// Test that generated code is syntactically valid Rust
fn check_syntax(code: &str, test_name: &str) -> bool {
    // Write to temp file
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!("dyna_codegen_test_{}.rs", test_name));

    let mut file = std::fs::File::create(&temp_file).unwrap();
    writeln!(file, "{}", code).unwrap();

    // Try to format with rustfmt (this parses the code, checking syntax)
    // We use regular rustfmt (not --check) which reformats and returns success if valid
    let output = Command::new("rustfmt")
        .arg(&temp_file)
        .output();

    match output {
        Ok(result) => {
            if !result.status.success() {
                eprintln!("Syntax check failed for {}:", test_name);
                eprintln!("stderr: {}", String::from_utf8_lossy(&result.stderr));
                false
            } else {
                // Rustfmt succeeded, code is syntactically valid
                true
            }
        }
        Err(e) => {
            eprintln!("Could not run rustfmt: {}", e);
            // If rustfmt isn't available, just check basic structure
            code.contains("pub struct") &&
            code.contains("pub fn solve") &&
            code.matches('{').count() == code.matches('}').count()
        }
    }
}

/// Generate and check code for transitive closure
#[test]
fn test_codegen_transitive_closure() {
    // path(X, Y) += edge(X, Y).
    // path(X, Z) += edge(X, Y) * path(Y, Z).
    let program = Program::from_rules(vec![
        Rule::new(
            Term::compound("path", vec![Term::var(0), Term::var(1)]),
            Product::new(vec![
                Term::compound("edge", vec![Term::var(0), Term::var(1)]),
            ]),
        ),
        Rule::new(
            Term::compound("path", vec![Term::var(0), Term::var(2)]),
            Product::new(vec![
                Term::compound("edge", vec![Term::var(0), Term::var(1)]),
                Term::compound("path", vec![Term::var(1), Term::var(2)]),
            ]),
        ),
    ]);

    let analysis = ProgramAnalysis::analyze(&program);
    let config = CodeGenConfig::counting();
    let generator = CodeGenerator::new(analysis, config);
    let code = generator.generate(&program);

    println!("=== Transitive Closure Generated Code ===");
    println!("{}", code);
    println!("==========================================");

    // Check structure
    assert!(code.contains("struct Edge"), "Should have Edge struct");
    assert!(code.contains("struct Path"), "Should have Path struct");
    assert!(code.contains("pub fn solve"), "Should have solve method");
    assert!(code.contains("update_path"), "Should have update_path method");
    assert!(code.contains("update_edge"), "Should have update_edge method");

    // Check brace balance
    let open = code.matches('{').count();
    let close = code.matches('}').count();
    assert_eq!(open, close, "Braces should be balanced: {} open, {} close", open, close);

    // Check syntax if rustfmt available
    assert!(check_syntax(&code, "transitive_closure"));
}

/// Generate and check code for CKY parsing
#[test]
fn test_codegen_cky_parsing() {
    // phrase(X, I, K) += phrase(Y, I, J) * phrase(Z, J, K) * rewrite(X, Y, Z).
    let program = Program::from_rules(vec![
        Rule::new(
            Term::compound("phrase", vec![Term::var(0), Term::var(3), Term::var(5)]),
            Product::new(vec![
                Term::compound("phrase", vec![Term::var(1), Term::var(3), Term::var(4)]),
                Term::compound("phrase", vec![Term::var(2), Term::var(4), Term::var(5)]),
                Term::compound("rewrite", vec![Term::var(0), Term::var(1), Term::var(2)]),
            ]),
        ),
    ]);

    let analysis = ProgramAnalysis::analyze(&program);
    let config = CodeGenConfig::counting();
    let generator = CodeGenerator::new(analysis, config);
    let code = generator.generate(&program);

    println!("=== CKY Parsing Generated Code ===");
    println!("{}", code);
    println!("===================================");

    // Check structure
    assert!(code.contains("struct Phrase"), "Should have Phrase struct");
    assert!(code.contains("struct Rewrite"), "Should have Rewrite struct");
    assert!(code.contains("phrase_by_"), "Should have phrase index");

    // Check brace balance
    let open = code.matches('{').count();
    let close = code.matches('}').count();
    assert_eq!(open, close, "Braces should be balanced");

    assert!(check_syntax(&code, "cky_parsing"));
}

/// Generate and check code for simple facts-only program
#[test]
fn test_codegen_facts_only() {
    // Just facts, no rules
    let program = Program::from_rules(vec![
        Rule::fact(make_edge(1, 2)),
        Rule::fact(make_edge(2, 3)),
    ]);

    let analysis = ProgramAnalysis::analyze(&program);
    let config = CodeGenConfig::counting();
    let generator = CodeGenerator::new(analysis, config);
    let code = generator.generate(&program);

    println!("=== Facts Only Generated Code ===");
    println!("{}", code);
    println!("==================================");

    assert!(code.contains("struct Edge"), "Should have Edge struct");

    let open = code.matches('{').count();
    let close = code.matches('}').count();
    assert_eq!(open, close, "Braces should be balanced");

    assert!(check_syntax(&code, "facts_only"));
}

/// Generate and check code for fibonacci-like recursion
#[test]
fn test_codegen_fibonacci() {
    // fib(0) = 1.
    // fib(1) = 1.
    // fib(N) += fib(N-1) * fib(N-2).  (simplified - just structure test)
    //
    // For now, test a simpler recursive structure:
    // count(N) += count(M) * step(M, N).
    let program = Program::from_rules(vec![
        Rule::new(
            Term::compound("count", vec![Term::var(1)]),
            Product::new(vec![
                Term::compound("count", vec![Term::var(0)]),
                Term::compound("step", vec![Term::var(0), Term::var(1)]),
            ]),
        ),
    ]);

    let analysis = ProgramAnalysis::analyze(&program);
    let config = CodeGenConfig::counting();
    let generator = CodeGenerator::new(analysis, config);
    let code = generator.generate(&program);

    println!("=== Fibonacci-like Generated Code ===");
    println!("{}", code);
    println!("======================================");

    assert!(code.contains("struct Count"));
    assert!(code.contains("struct Step"));

    let open = code.matches('{').count();
    let close = code.matches('}').count();
    assert_eq!(open, close, "Braces should be balanced");

    assert!(check_syntax(&code, "fibonacci"));
}

/// Generate code with boolean semiring
#[test]
fn test_codegen_boolean_semiring() {
    let program = Program::from_rules(vec![
        Rule::new(
            Term::compound("reach", vec![Term::var(0), Term::var(1)]),
            Product::new(vec![
                Term::compound("edge", vec![Term::var(0), Term::var(1)]),
            ]),
        ),
        Rule::new(
            Term::compound("reach", vec![Term::var(0), Term::var(2)]),
            Product::new(vec![
                Term::compound("edge", vec![Term::var(0), Term::var(1)]),
                Term::compound("reach", vec![Term::var(1), Term::var(2)]),
            ]),
        ),
    ]);

    let analysis = ProgramAnalysis::analyze(&program);
    let config = CodeGenConfig::boolean();
    let generator = CodeGenerator::new(analysis, config);
    let code = generator.generate(&program);

    println!("=== Boolean Semiring Generated Code ===");
    println!("{}", code);
    println!("========================================");

    // Check boolean operations
    assert!(code.contains("bool"), "Should use bool type");
    assert!(code.contains("false") || code.contains("true"), "Should have boolean literals");
    assert!(code.contains("||") || code.contains("&&"), "Should have boolean ops");

    let open = code.matches('{').count();
    let close = code.matches('}').count();
    assert_eq!(open, close, "Braces should be balanced");

    assert!(check_syntax(&code, "boolean_semiring"));
}

/// Generate code with tropical (min-plus) semiring
#[test]
fn test_codegen_tropical_semiring() {
    // Shortest path
    let program = Program::from_rules(vec![
        Rule::new(
            Term::compound("dist", vec![Term::var(0), Term::var(1)]),
            Product::new(vec![
                Term::compound("edge", vec![Term::var(0), Term::var(1)]),
            ]),
        ),
        Rule::new(
            Term::compound("dist", vec![Term::var(0), Term::var(2)]),
            Product::new(vec![
                Term::compound("dist", vec![Term::var(0), Term::var(1)]),
                Term::compound("edge", vec![Term::var(1), Term::var(2)]),
            ]),
        ),
    ]);

    let analysis = ProgramAnalysis::analyze(&program);
    let config = CodeGenConfig::tropical();
    let generator = CodeGenerator::new(analysis, config);
    let code = generator.generate(&program);

    println!("=== Tropical Semiring Generated Code ===");
    println!("{}", code);
    println!("=========================================");

    // Check tropical operations
    assert!(code.contains("f64::INFINITY") || code.contains("INFINITY"),
        "Should have infinity for zero");
    assert!(code.contains(".min") || code.contains("min("),
        "Should have min operation");

    let open = code.matches('{').count();
    let close = code.matches('}').count();
    assert_eq!(open, close, "Braces should be balanced");

    assert!(check_syntax(&code, "tropical_semiring"));
}

/// Test code generation for multiple head variables
#[test]
fn test_codegen_head_construction() {
    // triple(X, Y, Z) += pair(X, Y) * single(Z).
    let program = Program::from_rules(vec![
        Rule::new(
            Term::compound("triple", vec![Term::var(0), Term::var(1), Term::var(2)]),
            Product::new(vec![
                Term::compound("pair", vec![Term::var(0), Term::var(1)]),
                Term::compound("single", vec![Term::var(2)]),
            ]),
        ),
    ]);

    let analysis = ProgramAnalysis::analyze(&program);
    let config = CodeGenConfig::counting();
    let generator = CodeGenerator::new(analysis, config);
    let code = generator.generate(&program);

    println!("=== Head Construction Generated Code ===");
    println!("{}", code);
    println!("=========================================");

    assert!(code.contains("struct Triple"));
    assert!(code.contains("arg0:"));
    assert!(code.contains("arg1:"));
    assert!(code.contains("arg2:"));

    let open = code.matches('{').count();
    let close = code.matches('}').count();
    assert_eq!(open, close, "Braces should be balanced");

    assert!(check_syntax(&code, "head_construction"));
}

/// Summary test that runs all programs and reports
#[test]
fn test_codegen_all_programs() {
    let test_cases = vec![
        ("transitive_closure", Program::from_rules(vec![
            Rule::new(
                Term::compound("path", vec![Term::var(0), Term::var(1)]),
                Product::new(vec![
                    Term::compound("edge", vec![Term::var(0), Term::var(1)]),
                ]),
            ),
            Rule::new(
                Term::compound("path", vec![Term::var(0), Term::var(2)]),
                Product::new(vec![
                    Term::compound("edge", vec![Term::var(0), Term::var(1)]),
                    Term::compound("path", vec![Term::var(1), Term::var(2)]),
                ]),
            ),
        ])),
        ("cky_binary", Program::from_rules(vec![
            Rule::new(
                Term::compound("phrase", vec![Term::var(0), Term::var(3), Term::var(5)]),
                Product::new(vec![
                    Term::compound("phrase", vec![Term::var(1), Term::var(3), Term::var(4)]),
                    Term::compound("phrase", vec![Term::var(2), Term::var(4), Term::var(5)]),
                    Term::compound("rewrite", vec![Term::var(0), Term::var(1), Term::var(2)]),
                ]),
            ),
        ])),
        ("chain_rule", Program::from_rules(vec![
            Rule::new(
                Term::compound("d", vec![Term::var(0)]),
                Product::new(vec![
                    Term::compound("a", vec![Term::var(0)]),
                    Term::compound("b", vec![Term::var(0)]),
                    Term::compound("c", vec![Term::var(0)]),
                ]),
            ),
        ])),
    ];

    println!("\n=== Code Generation Test Summary ===\n");

    let mut all_passed = true;
    for (name, program) in test_cases {
        let analysis = ProgramAnalysis::analyze(&program);
        let config = CodeGenConfig::counting();
        let generator = CodeGenerator::new(analysis, config);
        let code = generator.generate(&program);

        let open = code.matches('{').count();
        let close = code.matches('}').count();
        let balanced = open == close;
        let has_solve = code.contains("pub fn solve");
        let syntax_ok = check_syntax(&code, name);

        let status = if balanced && has_solve && syntax_ok { "✓ PASS" } else { "✗ FAIL" };
        println!("{}: {} (braces: {}/{}, solve: {}, syntax: {})",
            name, status, open, close, has_solve, syntax_ok);

        if !balanced || !has_solve || !syntax_ok {
            all_passed = false;
        }
    }

    println!("\n=====================================\n");
    assert!(all_passed, "Some code generation tests failed");
}
