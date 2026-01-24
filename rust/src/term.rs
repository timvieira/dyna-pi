//! Core term representation for Dyna.
//!
//! This module provides the fundamental data structures for representing
//! terms, variables, and values in Dyna programs.

use ordered_float::OrderedFloat;
use rustc_hash::FxHashSet;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

/// Unique identifier for variables.
pub type VarId = u32;

/// Atomic values in Dyna.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Value {
    Int(i64),
    Float(OrderedFloat<f64>),
    Str(Rc<str>),
    Bool(bool),
    /// Symbol/atom (like Prolog atoms)
    Symbol(Rc<str>),
}

impl Value {
    pub fn int(n: i64) -> Self {
        Value::Int(n)
    }

    pub fn float(f: f64) -> Self {
        Value::Float(OrderedFloat(f))
    }

    pub fn str(s: impl Into<Rc<str>>) -> Self {
        Value::Str(s.into())
    }

    pub fn symbol(s: impl Into<Rc<str>>) -> Self {
        Value::Symbol(s.into())
    }

    pub fn bool(b: bool) -> Self {
        Value::Bool(b)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Float(x) => write!(f, "{}", x),
            Value::Str(s) => write!(f, "\"{}\"", s),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Symbol(s) => write!(f, "{}", s),
        }
    }
}

/// A term in Dyna - either a variable, constant, or compound term.
#[derive(Clone, Debug)]
pub enum Term {
    /// A logic variable
    Var(VarId),
    /// A constant value
    Const(Value),
    /// A compound term with functor and arguments
    Compound {
        functor: Rc<str>,
        args: Vec<Term>,
    },
}

impl Term {
    /// Create a new variable term.
    pub fn var(id: VarId) -> Self {
        Term::Var(id)
    }

    /// Create a new constant term.
    pub fn constant(v: Value) -> Self {
        Term::Const(v)
    }

    /// Create a new compound term.
    pub fn compound(functor: impl Into<Rc<str>>, args: Vec<Term>) -> Self {
        Term::Compound {
            functor: functor.into(),
            args,
        }
    }

    /// Create a compound term with no arguments (an atom).
    pub fn atom(name: impl Into<Rc<str>>) -> Self {
        Term::Compound {
            functor: name.into(),
            args: Vec::new(),
        }
    }

    /// Get the functor name if this is a compound term.
    pub fn functor(&self) -> Option<&str> {
        match self {
            Term::Compound { functor, .. } => Some(functor),
            _ => None,
        }
    }

    /// Get the arguments if this is a compound term.
    pub fn args(&self) -> Option<&[Term]> {
        match self {
            Term::Compound { args, .. } => Some(args),
            _ => None,
        }
    }

    /// Get the arity (number of arguments) of this term.
    pub fn arity(&self) -> usize {
        match self {
            Term::Compound { args, .. } => args.len(),
            _ => 0,
        }
    }

    /// Get functor and arity as a pair.
    pub fn functor_arity(&self) -> Option<(Rc<str>, usize)> {
        match self {
            Term::Compound { functor, args } => Some((functor.clone(), args.len())),
            _ => None,
        }
    }

    /// Check if this term contains no unbound variables.
    pub fn is_ground(&self) -> bool {
        match self {
            Term::Var(_) => false,
            Term::Const(_) => true,
            Term::Compound { args, .. } => args.iter().all(|a| a.is_ground()),
        }
    }

    /// Collect all variable IDs in this term.
    pub fn vars(&self) -> FxHashSet<VarId> {
        let mut result = FxHashSet::default();
        self.collect_vars(&mut result);
        result
    }

    fn collect_vars(&self, result: &mut FxHashSet<VarId>) {
        match self {
            Term::Var(v) => {
                result.insert(*v);
            }
            Term::Const(_) => {}
            Term::Compound { args, .. } => {
                for arg in args {
                    arg.collect_vars(result);
                }
            }
        }
    }

    /// Check if this term is a variable.
    pub fn is_var(&self) -> bool {
        matches!(self, Term::Var(_))
    }

    /// Check if this term is a constant.
    pub fn is_const(&self) -> bool {
        matches!(self, Term::Const(_))
    }

    /// Check if this term is a compound term.
    pub fn is_compound(&self) -> bool {
        matches!(self, Term::Compound { .. })
    }

    /// Get the variable ID if this is a variable.
    pub fn as_var(&self) -> Option<VarId> {
        match self {
            Term::Var(v) => Some(*v),
            _ => None,
        }
    }

    /// Get the constant value if this is a constant.
    pub fn as_const(&self) -> Option<&Value> {
        match self {
            Term::Const(v) => Some(v),
            _ => None,
        }
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Term::Var(a), Term::Var(b)) => a == b,
            (Term::Const(a), Term::Const(b)) => a == b,
            (
                Term::Compound {
                    functor: f1,
                    args: a1,
                },
                Term::Compound {
                    functor: f2,
                    args: a2,
                },
            ) => f1 == f2 && a1.len() == a2.len() && a1.iter().zip(a2.iter()).all(|(x, y)| x == y),
            _ => false,
        }
    }
}

impl Eq for Term {}

impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Term::Var(v) => v.hash(state),
            Term::Const(c) => c.hash(state),
            Term::Compound { functor, args } => {
                functor.hash(state);
                args.len().hash(state);
                for arg in args {
                    arg.hash(state);
                }
            }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(v) => write!(f, "_{}", v),
            Term::Const(c) => write!(f, "{}", c),
            Term::Compound { functor, args } if args.is_empty() => {
                write!(f, "{}", functor)
            }
            Term::Compound { functor, args } => {
                write!(f, "{}(", functor)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}

/// A product (tuple) of terms, used for rule bodies.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Product(pub Vec<Term>);

impl Product {
    pub fn new(terms: Vec<Term>) -> Self {
        Product(terms)
    }

    pub fn empty() -> Self {
        Product(Vec::new())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Term> {
        self.0.iter()
    }

    pub fn get(&self, index: usize) -> Option<&Term> {
        self.0.get(index)
    }

    /// Check if all terms in the product are ground.
    pub fn is_ground(&self) -> bool {
        self.0.iter().all(|t| t.is_ground())
    }

    /// Collect all variables in the product.
    pub fn vars(&self) -> FxHashSet<VarId> {
        let mut result = FxHashSet::default();
        for term in &self.0 {
            term.collect_vars(&mut result);
        }
        result
    }

    /// Concatenate two products.
    pub fn concat(&self, other: &Product) -> Product {
        let mut terms = self.0.clone();
        terms.extend(other.0.iter().cloned());
        Product(terms)
    }
}

impl std::ops::Index<usize> for Product {
    type Output = Term;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl IntoIterator for Product {
    type Item = Term;
    type IntoIter = std::vec::IntoIter<Term>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a Product {
    type Item = &'a Term;
    type IntoIter = std::slice::Iter<'a, Term>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl fmt::Display for Product {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, term) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", term)?;
        }
        write!(f, ")")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_term_creation() {
        let x = Term::var(0);
        assert!(x.is_var());
        assert!(!x.is_ground());

        let c = Term::constant(Value::int(42));
        assert!(c.is_const());
        assert!(c.is_ground());

        let f = Term::compound("f", vec![Term::var(0), Term::constant(Value::int(1))]);
        assert!(f.is_compound());
        assert!(!f.is_ground());
        assert_eq!(f.functor(), Some("f"));
        assert_eq!(f.arity(), 2);
    }

    #[test]
    fn test_term_equality() {
        let t1 = Term::compound("f", vec![Term::var(0)]);
        let t2 = Term::compound("f", vec![Term::var(0)]);
        let t3 = Term::compound("f", vec![Term::var(1)]);

        assert_eq!(t1, t2);
        assert_ne!(t1, t3);
    }

    #[test]
    fn test_term_vars() {
        let t = Term::compound(
            "f",
            vec![
                Term::var(0),
                Term::compound("g", vec![Term::var(1), Term::var(0)]),
            ],
        );
        let vars = t.vars();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&0));
        assert!(vars.contains(&1));
    }

    #[test]
    fn test_product() {
        let p = Product::new(vec![
            Term::var(0),
            Term::constant(Value::int(1)),
            Term::compound("f", vec![Term::var(1)]),
        ]);
        assert_eq!(p.len(), 3);
        assert!(!p.is_ground());

        let vars = p.vars();
        assert!(vars.contains(&0));
        assert!(vars.contains(&1));
    }

    #[test]
    fn test_term_display() {
        let t = Term::compound(
            "foo",
            vec![Term::var(0), Term::constant(Value::int(42))],
        );
        assert_eq!(format!("{}", t), "foo(_0, 42)");
    }
}
