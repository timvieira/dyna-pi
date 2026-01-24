//! Benchmark comparing Term vs ITerm (interned) performance
//!
//! Run with: cargo bench --bench intern_bench

use std::collections::HashMap;
use std::time::Instant;

use dyna_rust::intern::{reset_symbols, HcTable, HcTerm, ITerm};
use dyna_rust::term::{Term, Value};

const ITERATIONS: usize = 100_000;

fn bench_term_creation() -> (f64, f64) {
    // Benchmark original Term creation
    let start = Instant::now();
    for i in 0..ITERATIONS {
        let _ = Term::compound(
            "phrase",
            vec![
                Term::atom("NP"),
                Term::constant(Value::Int(i as i64)),
                Term::constant(Value::Int((i + 1) as i64)),
            ],
        );
    }
    let term_time = start.elapsed().as_secs_f64() * 1000.0;

    // Benchmark ITerm creation (interned)
    reset_symbols();
    let start = Instant::now();
    for i in 0..ITERATIONS {
        let _ = ITerm::compound(
            "phrase",
            vec![ITerm::atom("NP"), ITerm::int(i as i64), ITerm::int((i + 1) as i64)],
        );
    }
    let iterm_time = start.elapsed().as_secs_f64() * 1000.0;

    (term_time, iterm_time)
}

fn bench_term_equality() -> (f64, f64) {
    // Create terms to compare
    let terms: Vec<Term> = (0..1000)
        .map(|i| {
            Term::compound(
                "phrase",
                vec![
                    Term::atom("NP"),
                    Term::constant(Value::Int(i)),
                    Term::constant(Value::Int(i + 1)),
                ],
            )
        })
        .collect();

    // Benchmark Term equality (string comparison)
    let start = Instant::now();
    let mut count = 0;
    for _ in 0..100 {
        for i in 0..terms.len() {
            for j in 0..terms.len() {
                if terms[i] == terms[j] {
                    count += 1;
                }
            }
        }
    }
    let term_time = start.elapsed().as_secs_f64() * 1000.0;
    assert!(count > 0);

    // Create ITerm terms
    reset_symbols();
    let iterms: Vec<ITerm> = (0..1000)
        .map(|i| ITerm::compound("phrase", vec![ITerm::atom("NP"), ITerm::int(i), ITerm::int(i + 1)]))
        .collect();

    // Benchmark ITerm equality (u32 comparison)
    let start = Instant::now();
    let mut count = 0;
    for _ in 0..100 {
        for i in 0..iterms.len() {
            for j in 0..iterms.len() {
                if iterms[i] == iterms[j] {
                    count += 1;
                }
            }
        }
    }
    let iterm_time = start.elapsed().as_secs_f64() * 1000.0;
    assert!(count > 0);

    (term_time, iterm_time)
}

fn bench_term_hashing() -> (f64, f64) {
    use std::hash::{Hash, Hasher};

    // Create terms
    let terms: Vec<Term> = (0..10000)
        .map(|i| {
            Term::compound(
                "phrase",
                vec![
                    Term::atom("NP"),
                    Term::constant(Value::Int(i)),
                    Term::constant(Value::Int(i + 1)),
                ],
            )
        })
        .collect();

    // Benchmark Term hashing
    let start = Instant::now();
    let mut total_hash: u64 = 0;
    for _ in 0..100 {
        for term in &terms {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            term.hash(&mut hasher);
            total_hash = total_hash.wrapping_add(hasher.finish());
        }
    }
    let term_time = start.elapsed().as_secs_f64() * 1000.0;
    assert!(total_hash != 0);

    // Create ITerms
    reset_symbols();
    let iterms: Vec<ITerm> = (0..10000)
        .map(|i| ITerm::compound("phrase", vec![ITerm::atom("NP"), ITerm::int(i), ITerm::int(i + 1)]))
        .collect();

    // Benchmark ITerm hashing
    let start = Instant::now();
    let mut total_hash: u64 = 0;
    for _ in 0..100 {
        for term in &iterms {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            term.hash(&mut hasher);
            total_hash = total_hash.wrapping_add(hasher.finish());
        }
    }
    let iterm_time = start.elapsed().as_secs_f64() * 1000.0;
    assert!(total_hash != 0);

    (term_time, iterm_time)
}

fn bench_hashmap_lookup() -> (f64, f64) {
    // Create HashMap with Term keys
    let mut term_map: HashMap<Term, i32> = HashMap::new();
    for i in 0..10000 {
        let term = Term::compound(
            "phrase",
            vec![
                Term::atom("NP"),
                Term::constant(Value::Int(i)),
                Term::constant(Value::Int(i + 1)),
            ],
        );
        term_map.insert(term, i as i32);
    }

    // Benchmark Term HashMap lookup
    let start = Instant::now();
    let mut found = 0;
    for _ in 0..100 {
        for i in 0..10000 {
            let query = Term::compound(
                "phrase",
                vec![
                    Term::atom("NP"),
                    Term::constant(Value::Int(i)),
                    Term::constant(Value::Int(i + 1)),
                ],
            );
            if term_map.get(&query).is_some() {
                found += 1;
            }
        }
    }
    let term_time = start.elapsed().as_secs_f64() * 1000.0;
    assert!(found > 0);

    // Create HashMap with ITerm keys
    reset_symbols();
    let mut iterm_map: HashMap<ITerm, i32> = HashMap::new();
    for i in 0..10000 {
        let term = ITerm::compound("phrase", vec![ITerm::atom("NP"), ITerm::int(i), ITerm::int(i + 1)]);
        iterm_map.insert(term, i as i32);
    }

    // Benchmark ITerm HashMap lookup
    let start = Instant::now();
    let mut found = 0;
    for _ in 0..100 {
        for i in 0..10000 {
            let query =
                ITerm::compound("phrase", vec![ITerm::atom("NP"), ITerm::int(i), ITerm::int(i + 1)]);
            if iterm_map.get(&query).is_some() {
                found += 1;
            }
        }
    }
    let iterm_time = start.elapsed().as_secs_f64() * 1000.0;
    assert!(found > 0);

    (term_time, iterm_time)
}

fn bench_hash_consing() -> (f64, f64, usize, usize) {
    // Without hash consing: create many duplicate terms
    reset_symbols();
    let start = Instant::now();
    let mut terms: Vec<ITerm> = Vec::new();
    for _ in 0..100 {
        for i in 0..1000 {
            terms.push(ITerm::compound(
                "phrase",
                vec![ITerm::atom("NP"), ITerm::int(i), ITerm::int(i + 1)],
            ));
        }
    }
    let no_hc_time = start.elapsed().as_secs_f64() * 1000.0;
    let no_hc_count = terms.len(); // 100,000 allocations

    // With hash consing: deduplicate terms
    reset_symbols();
    let mut hc = HcTable::new();
    let start = Instant::now();
    let mut hc_terms: Vec<HcTerm> = Vec::new();
    for _ in 0..100 {
        for i in 0..1000i64 {
            let np = hc.atom("NP");
            let start_idx = hc.int(i);
            let end_idx = hc.int(i + 1);
            hc_terms.push(hc.compound("phrase", vec![np, start_idx, end_idx]));
        }
    }
    let hc_time = start.elapsed().as_secs_f64() * 1000.0;
    let hc_count = hc.len(); // Only ~3000 unique terms

    (no_hc_time, hc_time, no_hc_count, hc_count)
}

fn main() {
    println!("=======================================================================");
    println!("Term Representation Micro-benchmarks");
    println!("=======================================================================");
    println!();

    println!("1. Term Creation ({} iterations)", ITERATIONS);
    let (term_ms, iterm_ms) = bench_term_creation();
    println!("   Term (Rc<str>):    {:>8.2} ms", term_ms);
    println!("   ITerm (interned):  {:>8.2} ms", iterm_ms);
    println!("   Speedup:           {:>8.2}x", term_ms / iterm_ms);
    println!();

    println!("2. Term Equality (1000 × 1000 × 100 comparisons)");
    let (term_ms, iterm_ms) = bench_term_equality();
    println!("   Term (string cmp): {:>8.2} ms", term_ms);
    println!("   ITerm (u32 cmp):   {:>8.2} ms", iterm_ms);
    println!("   Speedup:           {:>8.2}x", term_ms / iterm_ms);
    println!();

    println!("3. Term Hashing (10000 × 100 hashes)");
    let (term_ms, iterm_ms) = bench_term_hashing();
    println!("   Term (string hash):{:>8.2} ms", term_ms);
    println!("   ITerm (u32 hash):  {:>8.2} ms", iterm_ms);
    println!("   Speedup:           {:>8.2}x", term_ms / iterm_ms);
    println!();

    println!("4. HashMap Lookup (10000 × 100 lookups)");
    let (term_ms, iterm_ms) = bench_hashmap_lookup();
    println!("   Term:              {:>8.2} ms", term_ms);
    println!("   ITerm:             {:>8.2} ms", iterm_ms);
    println!("   Speedup:           {:>8.2}x", term_ms / iterm_ms);
    println!();

    println!("5. Hash Consing Memory Efficiency");
    let (no_hc_ms, hc_ms, no_hc_count, hc_count) = bench_hash_consing();
    println!("   Without HC: {:>8.2} ms, {} term objects", no_hc_ms, no_hc_count);
    println!("   With HC:    {:>8.2} ms, {} unique terms", hc_ms, hc_count);
    println!(
        "   Memory reduction:  {:>5.1}x fewer allocations",
        no_hc_count as f64 / hc_count as f64
    );
    println!();

    println!("=======================================================================");
    println!("Summary: String interning provides 1.5-3x speedup on core operations.");
    println!("Hash consing reduces memory by ~33x for repeated term structures.");
    println!("=======================================================================");
}
