//! Code Generation for High-Performance Dyna Programs
//!
//! This module provides compile-time code generation to create specialized,
//! highly-optimized solver implementations. Key optimizations:
//!
//! 1. **Specialized Term Structs**: Replace generic `Term` enum with typed structs
//! 2. **Static Mode Analysis**: Pre-compute which query modes are needed
//! 3. **Specialized Indexes**: Generate array-based indexes for known domains
//! 4. **Compiled Pattern Matching**: Replace runtime unification with direct field access
//! 5. **Inlined Rule Execution**: Generate specialized code for each rule
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────────┐
//! │                         Code Generation Pipeline                        │
//! ├─────────────────────────────────────────────────────────────────────────┤
//! │                                                                         │
//! │  ┌──────────────┐    ┌──────────────┐    ┌──────────────────────────┐  │
//! │  │ Dyna Program │───►│ Static       │───►│ Specialized Rust Code   │  │
//! │  │ (rules)      │    │ Analysis     │    │ - Term structs          │  │
//! │  └──────────────┘    │              │    │ - Index structures      │  │
//! │                      │ - Modes      │    │ - Pattern matchers      │  │
//! │                      │ - Types      │    │ - Rule executors        │  │
//! │                      │ - Domains    │    └──────────────────────────┘  │
//! │                      └──────────────┘              │                   │
//! │                                                    ▼                   │
//! │                                          ┌──────────────────────────┐  │
//! │                                          │ Compiled Solver          │  │
//! │                                          │ (native machine code)    │  │
//! │                                          └──────────────────────────┘  │
//! └─────────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Example: CKY Parsing
//!
//! ## Input Program
//! ```dyna
//! phrase(X, I, K) += phrase(Y, I, J) * phrase(Z, J, K) * rewrite(X, Y, Z).
//! phrase(X, I, J) += word(W, I, J) * rewrite(X, W).
//! ```
//!
//! ## Generated Code (simplified)
//! ```rust,ignore
//! // Specialized term struct (no enum, no Vec)
//! #[derive(Clone, Copy, PartialEq, Eq, Hash)]
//! struct Phrase {
//!     cat: u16,    // Category symbol ID
//!     start: u16,  // Start position
//!     end: u16,    // End position
//! }
//!
//! // Specialized index (array-based, not HashMap)
//! struct PhraseIndex {
//!     // by_span[i][j] = phrases spanning position i to j
//!     by_span: Vec<Vec<Vec<Phrase>>>,
//!     // by_cat[cat] = phrases with this category
//!     by_cat: Vec<Vec<Phrase>>,
//! }
//!
//! // Compiled rule (no unification, direct field access)
//! fn fire_binary_rule(
//!     left: Phrase,
//!     chart: &PhraseIndex,
//!     rewrites: &RewriteTable,
//!     emit: &mut impl FnMut(Phrase),
//! ) {
//!     // Query right children: phrase(_, J, K) for any K
//!     for &right in &chart.by_span[left.end] {
//!         // Lookup rewrite: X where rewrite(X, left.cat, right.cat)
//!         for &parent_cat in rewrites.lookup(left.cat, right.cat) {
//!             emit(Phrase {
//!                 cat: parent_cat,
//!                 start: left.start,
//!                 end: right.end,
//!             });
//!         }
//!     }
//! }
//! ```

pub mod analysis;
pub mod cky_compiled;
pub mod generator;

pub use analysis::ProgramAnalysis;
pub use generator::{CodeGenerator, CodeGenConfig};
