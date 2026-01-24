//! Static Analysis for Code Generation
//!
//! Analyzes Dyna programs to extract information needed for specialization:
//! - Functor signatures (name, arity, argument types)
//! - Query modes (which positions are bound in lookups)
//! - Domain bounds (range of values for each position)

use crate::rule::Program;
use crate::term::{Term, Value, VarId};
use rustc_hash::{FxHashMap, FxHashSet};
use std::rc::Rc;

/// Inferred type for a term position
#[derive(Clone, Debug)]
pub enum ArgType {
    /// Integer with optional known bounds
    Int { min: Option<i64>, max: Option<i64> },
    /// Symbol from a finite set
    Symbol { values: FxHashSet<Rc<str>> },
    /// Nested term with known functor
    Term { functor: Rc<str>, arity: usize },
    /// Unknown or mixed types
    Any,
}

impl ArgType {
    pub fn int() -> Self {
        ArgType::Int { min: None, max: None }
    }

    pub fn int_bounded(min: i64, max: i64) -> Self {
        ArgType::Int {
            min: Some(min),
            max: Some(max),
        }
    }

    pub fn symbol(name: &str) -> Self {
        let mut values = FxHashSet::default();
        values.insert(name.into());
        ArgType::Symbol { values }
    }

    /// Merge two types (union)
    pub fn merge(&self, other: &ArgType) -> ArgType {
        match (self, other) {
            (ArgType::Int { min: min1, max: max1 }, ArgType::Int { min: min2, max: max2 }) => {
                ArgType::Int {
                    min: match (min1, min2) {
                        (Some(a), Some(b)) => Some((*a).min(*b)),
                        _ => None,
                    },
                    max: match (max1, max2) {
                        (Some(a), Some(b)) => Some((*a).max(*b)),
                        _ => None,
                    },
                }
            }
            (ArgType::Symbol { values: v1 }, ArgType::Symbol { values: v2 }) => {
                let mut merged = v1.clone();
                merged.extend(v2.iter().cloned());
                ArgType::Symbol { values: merged }
            }
            (ArgType::Term { functor: f1, arity: a1 }, ArgType::Term { functor: f2, arity: a2 })
                if f1 == f2 && a1 == a2 =>
            {
                ArgType::Term {
                    functor: f1.clone(),
                    arity: *a1,
                }
            }
            _ => ArgType::Any,
        }
    }
}

/// Query mode: which argument positions are bound
pub type Mode = Vec<usize>;

/// Functor signature with inferred types
#[derive(Clone, Debug)]
pub struct FunctorSig {
    pub name: Rc<str>,
    pub arity: usize,
    pub arg_types: Vec<ArgType>,
    /// Query modes used for this functor
    pub modes: FxHashSet<Mode>,
}

/// Analysis result for a program
#[derive(Clone, Debug)]
pub struct ProgramAnalysis {
    /// Signatures for each (functor, arity) pair
    pub functors: FxHashMap<(Rc<str>, usize), FunctorSig>,
    /// Which rules drive which functors
    pub drivers: FxHashMap<(Rc<str>, usize), Vec<(usize, usize)>>,
    /// Maximum sentence length (for CKY-style programs)
    pub max_span: Option<usize>,
}

impl ProgramAnalysis {
    /// Analyze a Dyna program
    pub fn analyze(program: &Program) -> Self {
        let mut analysis = ProgramAnalysis {
            functors: FxHashMap::default(),
            drivers: FxHashMap::default(),
            max_span: None,
        };

        // First pass: collect all functors and their types from facts
        for rule in program.iter() {
            analysis.analyze_term(&rule.head, &FxHashMap::default());
            for subgoal in rule.body.iter() {
                analysis.analyze_term(subgoal, &FxHashMap::default());
            }
        }

        // Second pass: analyze query modes from rule bodies
        for (rule_idx, rule) in program.iter().enumerate() {
            for (subgoal_idx, subgoal) in rule.body.iter().enumerate() {
                if let Some(fa) = subgoal.functor_arity() {
                    // Record driver
                    analysis
                        .drivers
                        .entry(fa.clone())
                        .or_default()
                        .push((rule_idx, subgoal_idx));

                    // Analyze mode: which positions are bound when this subgoal is queried?
                    // This depends on which variables are bound by earlier subgoals
                    let bound_vars = Self::bound_vars_before(&rule.body, subgoal_idx);
                    let mode = Self::compute_mode(subgoal, &bound_vars);

                    if let Some(sig) = analysis.functors.get_mut(&fa) {
                        sig.modes.insert(mode);
                    }
                }
            }
        }

        // Detect CKY-style programs and infer max span
        analysis.detect_cky_pattern();

        analysis
    }

    fn analyze_term(&mut self, term: &Term, var_types: &FxHashMap<VarId, ArgType>) {
        if let Term::Compound { functor, args } = term {
            let fa = (functor.clone(), args.len());

            let sig = self.functors.entry(fa).or_insert_with(|| FunctorSig {
                name: functor.clone(),
                arity: args.len(),
                arg_types: vec![ArgType::Any; args.len()],
                modes: FxHashSet::default(),
            });

            // Infer types from arguments
            for (i, arg) in args.iter().enumerate() {
                let arg_type = match arg {
                    Term::Const(Value::Int(n)) => ArgType::int_bounded(*n, *n),
                    Term::Const(Value::Symbol(s)) => ArgType::symbol(s),
                    Term::Compound { functor, args } => ArgType::Term {
                        functor: functor.clone(),
                        arity: args.len(),
                    },
                    Term::Var(v) => var_types.get(v).cloned().unwrap_or(ArgType::Any),
                    _ => ArgType::Any,
                };

                sig.arg_types[i] = sig.arg_types[i].merge(&arg_type);
            }
        }
    }

    /// Compute which variables are bound before a given subgoal position
    fn bound_vars_before(body: &crate::term::Product, pos: usize) -> FxHashSet<VarId> {
        let mut bound = FxHashSet::default();
        for subgoal in body.iter().take(pos) {
            Self::collect_vars(subgoal, &mut bound);
        }
        bound
    }

    fn collect_vars(term: &Term, vars: &mut FxHashSet<VarId>) {
        match term {
            Term::Var(v) => {
                vars.insert(*v);
            }
            Term::Compound { args, .. } => {
                for arg in args {
                    Self::collect_vars(arg, vars);
                }
            }
            _ => {}
        }
    }

    /// Compute query mode: which positions are bound?
    fn compute_mode(term: &Term, bound_vars: &FxHashSet<VarId>) -> Mode {
        let mut mode = Vec::new();
        if let Term::Compound { args, .. } = term {
            for (i, arg) in args.iter().enumerate() {
                if Self::is_bound(arg, bound_vars) {
                    mode.push(i);
                }
            }
        }
        mode
    }

    fn is_bound(term: &Term, bound_vars: &FxHashSet<VarId>) -> bool {
        match term {
            Term::Var(v) => bound_vars.contains(v),
            Term::Const(_) => true,
            Term::Compound { args, .. } => args.iter().all(|a| Self::is_bound(a, bound_vars)),
        }
    }

    /// Detect CKY-style phrase(Cat, I, J) patterns
    fn detect_cky_pattern(&mut self) {
        // Look for phrase/3 or similar patterns with integer spans
        for ((name, arity), sig) in &self.functors {
            if *arity == 3 {
                // Check if positions 1 and 2 are integers (spans)
                if matches!(&sig.arg_types[1], ArgType::Int { .. })
                    && matches!(&sig.arg_types[2], ArgType::Int { .. })
                {
                    // Extract max span from integer bounds
                    if let ArgType::Int { max: Some(max), .. } = &sig.arg_types[2] {
                        self.max_span = Some((*max as usize).max(self.max_span.unwrap_or(0)));
                    }
                }
            }
        }
    }

    /// Generate a report of the analysis
    pub fn report(&self) -> String {
        let mut report = String::new();
        report.push_str("=== Program Analysis ===\n\n");

        report.push_str("Functors:\n");
        for ((name, arity), sig) in &self.functors {
            report.push_str(&format!("  {}/{}\n", name, arity));
            for (i, arg_type) in sig.arg_types.iter().enumerate() {
                report.push_str(&format!("    arg[{}]: {:?}\n", i, arg_type));
            }
            report.push_str(&format!("    modes: {:?}\n", sig.modes));
        }

        if let Some(max_span) = self.max_span {
            report.push_str(&format!("\nDetected CKY pattern, max span: {}\n", max_span));
        }

        report
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rule::Rule;
    use crate::term::Product;

    #[test]
    fn test_analyze_cky() {
        // phrase(X, I, K) += phrase(Y, I, J) * phrase(Z, J, K) * rewrite(X, Y, Z).
        let binary_rule = Rule::new(
            Term::compound("phrase", vec![Term::var(0), Term::var(3), Term::var(5)]),
            Product::new(vec![
                Term::compound("phrase", vec![Term::var(1), Term::var(3), Term::var(4)]),
                Term::compound("phrase", vec![Term::var(2), Term::var(4), Term::var(5)]),
                Term::compound(
                    "rewrite",
                    vec![Term::var(0), Term::var(1), Term::var(2)],
                ),
            ]),
        );

        // phrase(X, I, J) += word(W, I, J) * rewrite(X, W).
        let unary_rule = Rule::new(
            Term::compound("phrase", vec![Term::var(0), Term::var(3), Term::var(4)]),
            Product::new(vec![
                Term::compound("word", vec![Term::var(6), Term::var(3), Term::var(4)]),
                Term::compound("rewrite", vec![Term::var(0), Term::var(6)]),
            ]),
        );

        // Add some facts
        let edge_fact = Rule::fact(Term::compound(
            "word",
            vec![
                Term::atom("the"),
                Term::constant(Value::Int(0)),
                Term::constant(Value::Int(1)),
            ],
        ));

        let program = Program::from_rules(vec![binary_rule, unary_rule, edge_fact]);
        let analysis = ProgramAnalysis::analyze(&program);

        // Check that phrase/3 was found
        assert!(analysis.functors.contains_key(&("phrase".into(), 3)));

        // Check modes for phrase/3
        let phrase_sig = &analysis.functors[&("phrase".into(), 3)];
        // Modes should include:
        // - [1] (query by I - first subgoal of binary rule)
        // - [1, 2] (query by I, J - for matching word spans)
        assert!(!phrase_sig.modes.is_empty());

        println!("{}", analysis.report());
    }
}
