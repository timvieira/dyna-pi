//! Rule representation for Dyna programs.
//!
//! A rule consists of a head term and a body (product of subgoals).

use crate::subst::Subst;
use crate::term::{Product, Term, VarId};
use rustc_hash::FxHashSet;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

/// A Dyna rule: head += body[0] * body[1] * ... * body[n]
#[derive(Clone, Debug)]
pub struct Rule {
    /// The head of the rule
    pub head: Term,
    /// The body subgoals
    pub body: Product,
    /// Cached signature for fast comparison
    signature: Option<RuleSignature>,
}

/// Signature of a rule for fast equality checking.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RuleSignature {
    pub head_functor: Option<Rc<str>>,
    pub head_arity: usize,
    pub body_len: usize,
    pub body_functors: Vec<Option<Rc<str>>>,
    pub body_arities: Vec<usize>,
}

impl Rule {
    /// Create a new rule.
    pub fn new(head: Term, body: Product) -> Self {
        Rule {
            head,
            body,
            signature: None,
        }
    }

    /// Create a rule with no body (a fact).
    pub fn fact(head: Term) -> Self {
        Rule::new(head, Product::empty())
    }

    /// Create a rule with a single subgoal.
    pub fn unary(head: Term, subgoal: Term) -> Self {
        Rule::new(head, Product::new(vec![subgoal]))
    }

    /// Create a rule with two subgoals.
    pub fn binary(head: Term, subgoal1: Term, subgoal2: Term) -> Self {
        Rule::new(head, Product::new(vec![subgoal1, subgoal2]))
    }

    /// Get or compute the signature of this rule.
    pub fn signature(&self) -> RuleSignature {
        if let Some(sig) = &self.signature {
            return sig.clone();
        }

        RuleSignature {
            head_functor: self.head.functor().map(|s| s.into()),
            head_arity: self.head.arity(),
            body_len: self.body.len(),
            body_functors: self.body.iter().map(|t| t.functor().map(|s| s.into())).collect(),
            body_arities: self.body.iter().map(|t| t.arity()).collect(),
        }
    }

    /// Get the number of subgoals in the body.
    pub fn body_len(&self) -> usize {
        self.body.len()
    }

    /// Check if this is a fact (empty body).
    pub fn is_fact(&self) -> bool {
        self.body.is_empty()
    }

    /// Check if this is a linear rule (at most one subgoal).
    pub fn is_linear(&self) -> bool {
        self.body.len() <= 1
    }

    /// Get all variables in this rule.
    pub fn vars(&self) -> FxHashSet<VarId> {
        let mut vars = self.head.vars();
        for subgoal in &self.body {
            for v in subgoal.vars() {
                vars.insert(v);
            }
        }
        vars
    }

    /// Get variables that appear in the head.
    pub fn head_vars(&self) -> FxHashSet<VarId> {
        self.head.vars()
    }

    /// Get variables that appear only in the body.
    pub fn body_only_vars(&self) -> FxHashSet<VarId> {
        let head_vars = self.head_vars();
        let body_vars = self.body.vars();
        body_vars.difference(&head_vars).copied().collect()
    }

    /// Check if this rule is range-restricted (all head vars appear in body).
    pub fn is_range_restricted(&self) -> bool {
        let head_vars = self.head_vars();
        let body_vars = self.body.vars();
        head_vars.is_subset(&body_vars)
    }

    /// Check if the rule is ground (no variables).
    pub fn is_ground(&self) -> bool {
        self.head.is_ground() && self.body.is_ground()
    }

    /// Apply a substitution to this rule.
    pub fn apply(&self, subst: &Subst) -> Rule {
        Rule::new(subst.apply(&self.head), subst.apply_product(&self.body))
    }

    /// Freshen this rule with new variable names.
    pub fn fresh(&self, subst: &mut Subst) -> Rule {
        let mut var_map = rustc_hash::FxHashMap::default();
        let head = fresh_term(&self.head, subst, &mut var_map);
        let body = Product::new(
            self.body
                .iter()
                .map(|t| fresh_term(t, subst, &mut var_map))
                .collect(),
        );
        Rule::new(head, body)
    }

    /// Canonicalize variable names in order of first occurrence.
    pub fn canonicalize(&self) -> Rule {
        let mut var_map = rustc_hash::FxHashMap::default();
        let mut next = 0;

        let head = canon_term(&self.head, &mut var_map, &mut next);
        let body = Product::new(
            self.body
                .iter()
                .map(|t| canon_term(t, &mut var_map, &mut next))
                .collect(),
        );
        Rule::new(head, body)
    }

    /// Check if two rules are equal modulo variable renaming and subgoal reordering.
    pub fn same(&self, other: &Rule) -> bool {
        // Quick check: signatures must match
        if self.signature() != other.signature() {
            return false;
        }

        // Canonicalize and compare
        let c1 = self.canonicalize();
        let c2 = other.canonicalize();

        if c1.head != c2.head {
            return false;
        }

        // For bodies, we need to check modulo reordering
        // Simple case: same order
        if c1.body == c2.body {
            return true;
        }

        // TODO: Handle permutations for commutative matching
        // For now, require same order
        false
    }

    /// Get the "degree" of this rule (max variable occurrences for complexity analysis).
    pub fn degree(&self) -> usize {
        // Simplified: count total variable occurrences
        let mut count = 0;
        count_vars(&self.head, &mut count);
        for subgoal in &self.body {
            count_vars(subgoal, &mut count);
        }
        count
    }
}

fn fresh_term(
    term: &Term,
    subst: &mut Subst,
    var_map: &mut rustc_hash::FxHashMap<VarId, VarId>,
) -> Term {
    match term {
        Term::Var(v) => {
            let new_v = *var_map.entry(*v).or_insert_with(|| subst.fresh_var());
            Term::Var(new_v)
        }
        Term::Compound { functor, args } => Term::Compound {
            functor: functor.clone(),
            args: args.iter().map(|a| fresh_term(a, subst, var_map)).collect(),
        },
        Term::Const(_) => term.clone(),
    }
}

fn canon_term(
    term: &Term,
    var_map: &mut rustc_hash::FxHashMap<VarId, VarId>,
    next: &mut VarId,
) -> Term {
    match term {
        Term::Var(v) => {
            let new_v = *var_map.entry(*v).or_insert_with(|| {
                let id = *next;
                *next += 1;
                id
            });
            Term::Var(new_v)
        }
        Term::Compound { functor, args } => Term::Compound {
            functor: functor.clone(),
            args: args.iter().map(|a| canon_term(a, var_map, next)).collect(),
        },
        Term::Const(_) => term.clone(),
    }
}

fn count_vars(term: &Term, count: &mut usize) {
    match term {
        Term::Var(_) => *count += 1,
        Term::Compound { args, .. } => {
            for arg in args {
                count_vars(arg, count);
            }
        }
        Term::Const(_) => {}
    }
}

impl PartialEq for Rule {
    fn eq(&self, other: &Self) -> bool {
        self.head == other.head && self.body == other.body
    }
}

impl Eq for Rule {}

impl Hash for Rule {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.head.hash(state);
        self.body.hash(state);
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.head)?;
        if !self.body.is_empty() {
            write!(f, " += ")?;
            for (i, subgoal) in self.body.iter().enumerate() {
                if i > 0 {
                    write!(f, " * ")?;
                }
                write!(f, "{}", subgoal)?;
            }
        }
        write!(f, ".")
    }
}

/// A collection of rules forming a Dyna program.
#[derive(Clone, Debug, Default)]
pub struct Program {
    pub rules: Vec<Rule>,
}

impl Program {
    /// Create a new empty program.
    pub fn new() -> Self {
        Program { rules: Vec::new() }
    }

    /// Create a program from a list of rules.
    pub fn from_rules(rules: Vec<Rule>) -> Self {
        Program { rules }
    }

    /// Add a rule to the program.
    pub fn add_rule(&mut self, rule: Rule) {
        self.rules.push(rule);
    }

    /// Get the number of rules.
    pub fn len(&self) -> usize {
        self.rules.len()
    }

    /// Check if the program is empty.
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }

    /// Iterate over rules.
    pub fn iter(&self) -> impl Iterator<Item = &Rule> {
        self.rules.iter()
    }

    /// Get a rule by index.
    pub fn get(&self, index: usize) -> Option<&Rule> {
        self.rules.get(index)
    }

    /// Build an index from (functor, arity) to rules with that subgoal.
    pub fn build_driver_index(&self) -> DriverIndex {
        let mut index = DriverIndex::new();

        for (rule_idx, rule) in self.rules.iter().enumerate() {
            for (subgoal_idx, subgoal) in rule.body.iter().enumerate() {
                if let Some(fa) = subgoal.functor_arity() {
                    index
                        .0
                        .entry(fa)
                        .or_insert_with(Vec::new)
                        .push((rule_idx, subgoal_idx));
                }
            }
        }

        index
    }
}

/// Index from (functor, arity) to (rule_index, subgoal_index) pairs.
#[derive(Clone, Debug, Default)]
pub struct DriverIndex(pub rustc_hash::FxHashMap<(Rc<str>, usize), Vec<(usize, usize)>>);

impl DriverIndex {
    pub fn new() -> Self {
        DriverIndex(rustc_hash::FxHashMap::default())
    }

    pub fn get(&self, functor: &str, arity: usize) -> Option<&Vec<(usize, usize)>> {
        // Need to search by value since we have &str not Rc<str>
        for ((f, a), v) in &self.0 {
            if f.as_ref() == functor && *a == arity {
                return Some(v);
            }
        }
        None
    }

    pub fn get_by_term(&self, term: &Term) -> Option<&Vec<(usize, usize)>> {
        if let Some((f, a)) = term.functor_arity() {
            self.0.get(&(f, a))
        } else {
            None
        }
    }
}

impl IntoIterator for Program {
    type Item = Rule;
    type IntoIter = std::vec::IntoIter<Rule>;

    fn into_iter(self) -> Self::IntoIter {
        self.rules.into_iter()
    }
}

impl<'a> IntoIterator for &'a Program {
    type Item = &'a Rule;
    type IntoIter = std::slice::Iter<'a, Rule>;

    fn into_iter(self) -> Self::IntoIter {
        self.rules.iter()
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for rule in &self.rules {
            writeln!(f, "{}", rule)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Value;

    #[test]
    fn test_rule_creation() {
        let head = Term::compound("goal", vec![Term::var(0)]);
        let body = Product::new(vec![
            Term::compound("f", vec![Term::var(0), Term::var(1)]),
            Term::compound("g", vec![Term::var(1)]),
        ]);
        let rule = Rule::new(head, body);

        assert!(!rule.is_fact());
        assert!(!rule.is_linear());
        assert_eq!(rule.body_len(), 2);
    }

    #[test]
    fn test_rule_fact() {
        let fact = Rule::fact(Term::compound("base", vec![Term::constant(Value::Int(0))]));
        assert!(fact.is_fact());
        assert!(fact.is_linear());
    }

    #[test]
    fn test_rule_vars() {
        let rule = Rule::binary(
            Term::compound("h", vec![Term::var(0)]),
            Term::compound("f", vec![Term::var(0), Term::var(1)]),
            Term::compound("g", vec![Term::var(1), Term::var(2)]),
        );

        let vars = rule.vars();
        assert_eq!(vars.len(), 3);
        assert!(vars.contains(&0));
        assert!(vars.contains(&1));
        assert!(vars.contains(&2));

        let head_vars = rule.head_vars();
        assert_eq!(head_vars.len(), 1);
        assert!(head_vars.contains(&0));

        let body_only = rule.body_only_vars();
        assert_eq!(body_only.len(), 2);
        assert!(body_only.contains(&1));
        assert!(body_only.contains(&2));
    }

    #[test]
    fn test_rule_canonicalize() {
        let rule1 = Rule::binary(
            Term::compound("h", vec![Term::var(5)]),
            Term::compound("f", vec![Term::var(5), Term::var(10)]),
            Term::compound("g", vec![Term::var(10)]),
        );

        let rule2 = Rule::binary(
            Term::compound("h", vec![Term::var(0)]),
            Term::compound("f", vec![Term::var(0), Term::var(1)]),
            Term::compound("g", vec![Term::var(1)]),
        );

        let c1 = rule1.canonicalize();
        let c2 = rule2.canonicalize();

        assert_eq!(c1.head, c2.head);
        assert_eq!(c1.body, c2.body);
    }

    #[test]
    fn test_rule_signature() {
        let rule = Rule::binary(
            Term::compound("h", vec![Term::var(0)]),
            Term::compound("f", vec![Term::var(0), Term::var(1)]),
            Term::compound("g", vec![Term::var(1)]),
        );

        let sig = rule.signature();
        assert_eq!(sig.head_functor, Some("h".into()));
        assert_eq!(sig.head_arity, 1);
        assert_eq!(sig.body_len, 2);
    }

    #[test]
    fn test_program() {
        let mut program = Program::new();
        program.add_rule(Rule::fact(Term::compound(
            "base",
            vec![Term::constant(Value::Int(0))],
        )));
        program.add_rule(Rule::binary(
            Term::compound("path", vec![Term::var(0), Term::var(2)]),
            Term::compound("edge", vec![Term::var(0), Term::var(1)]),
            Term::compound("path", vec![Term::var(1), Term::var(2)]),
        ));

        assert_eq!(program.len(), 2);
    }

    #[test]
    fn test_driver_index() {
        let program = Program::from_rules(vec![
            Rule::binary(
                Term::compound("path", vec![Term::var(0), Term::var(2)]),
                Term::compound("edge", vec![Term::var(0), Term::var(1)]),
                Term::compound("path", vec![Term::var(1), Term::var(2)]),
            ),
            Rule::unary(
                Term::compound("reach", vec![Term::var(0)]),
                Term::compound("path", vec![Term::atom("start"), Term::var(0)]),
            ),
        ]);

        let index = program.build_driver_index();

        // edge(X, Y) drives rule 0 at position 0
        let edge_drivers = index.get("edge", 2).unwrap();
        assert_eq!(edge_drivers.len(), 1);
        assert_eq!(edge_drivers[0], (0, 0));

        // path(X, Y) drives rule 0 at position 1 and rule 1 at position 0
        let path_drivers = index.get("path", 2).unwrap();
        assert_eq!(path_drivers.len(), 2);
    }
}
