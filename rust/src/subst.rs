//! Substitution and unification for Dyna terms.
//!
//! This module provides the core unification algorithm and substitution
//! operations for logic programming.

use crate::term::{Product, Term, VarId};
use rustc_hash::FxHashMap;
use std::fmt;
use thiserror::Error;

/// Errors that can occur during unification.
#[derive(Debug, Clone, Error)]
pub enum UnifyError {
    #[error("occurs check failed: variable would create infinite term")]
    OccursCheck,
    #[error("terms do not unify: structural mismatch")]
    Mismatch,
}

/// A substitution mapping variables to terms.
#[derive(Clone, Debug, Default)]
pub struct Subst {
    bindings: FxHashMap<VarId, Term>,
    next_var: VarId,
}

impl Subst {
    /// Create a new empty substitution.
    pub fn new() -> Self {
        Subst {
            bindings: FxHashMap::default(),
            next_var: 0,
        }
    }

    /// Create a substitution with a starting variable counter.
    pub fn with_next_var(next_var: VarId) -> Self {
        Subst {
            bindings: FxHashMap::default(),
            next_var,
        }
    }

    /// Get the next fresh variable ID and increment counter.
    pub fn fresh_var(&mut self) -> VarId {
        let v = self.next_var;
        self.next_var += 1;
        v
    }

    /// Get the current next variable ID without incrementing.
    pub fn next_var_id(&self) -> VarId {
        self.next_var
    }

    /// Set the next variable ID counter.
    pub fn set_next_var(&mut self, id: VarId) {
        self.next_var = id;
    }

    /// Check if a variable is bound in this substitution.
    pub fn is_bound(&self, var: VarId) -> bool {
        self.bindings.contains_key(&var)
    }

    /// Get the binding for a variable, if any.
    pub fn get(&self, var: VarId) -> Option<&Term> {
        self.bindings.get(&var)
    }

    /// Bind a variable to a term.
    pub fn bind(&mut self, var: VarId, term: Term) {
        self.bindings.insert(var, term);
    }

    /// Number of bindings in the substitution.
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Check if the substitution is empty.
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Iterate over all bindings.
    pub fn iter(&self) -> impl Iterator<Item = (&VarId, &Term)> {
        self.bindings.iter()
    }

    /// Dereference a term, following variable bindings to their final value.
    pub fn deref(&self, term: &Term) -> Term {
        match term {
            Term::Var(v) => {
                if let Some(bound) = self.bindings.get(v) {
                    self.deref(bound)
                } else {
                    term.clone()
                }
            }
            Term::Compound { functor, args } => Term::Compound {
                functor: functor.clone(),
                args: args.iter().map(|a| self.deref(a)).collect(),
            },
            Term::Const(_) => term.clone(),
        }
    }

    /// Dereference one level only (don't recurse into compound terms).
    pub fn deref_shallow(&self, term: &Term) -> Term {
        match term {
            Term::Var(v) => {
                if let Some(bound) = self.bindings.get(v) {
                    self.deref_shallow(bound)
                } else {
                    term.clone()
                }
            }
            _ => term.clone(),
        }
    }

    /// Apply the substitution to a term (alias for deref).
    pub fn apply(&self, term: &Term) -> Term {
        self.deref(term)
    }

    /// Apply the substitution to a product.
    pub fn apply_product(&self, product: &Product) -> Product {
        Product::new(product.iter().map(|t| self.deref(t)).collect())
    }

    /// Occurs check: does variable `v` occur in term `t`?
    fn occurs_check(&self, v: VarId, term: &Term) -> bool {
        match self.deref(term) {
            Term::Var(u) => v == u,
            Term::Compound { args, .. } => args.iter().any(|a| self.occurs_check(v, a)),
            Term::Const(_) => false,
        }
    }

    /// Most General Unifier: unify two terms.
    ///
    /// This mutates the substitution to add new bindings.
    /// Returns Ok(()) on success, Err on failure.
    pub fn mgu(&mut self, x: &Term, y: &Term) -> Result<(), UnifyError> {
        let x = self.deref(x);
        let y = self.deref(y);

        match (&x, &y) {
            // Identical terms unify
            _ if x == y => Ok(()),

            // Variable cases
            (Term::Var(v), _) => {
                if self.occurs_check(*v, &y) {
                    Err(UnifyError::OccursCheck)
                } else {
                    self.bindings.insert(*v, y);
                    Ok(())
                }
            }
            (_, Term::Var(v)) => {
                if self.occurs_check(*v, &x) {
                    Err(UnifyError::OccursCheck)
                } else {
                    self.bindings.insert(*v, x);
                    Ok(())
                }
            }

            // Compound terms with same functor and arity
            (
                Term::Compound {
                    functor: f1,
                    args: a1,
                },
                Term::Compound {
                    functor: f2,
                    args: a2,
                },
            ) if f1 == f2 && a1.len() == a2.len() => {
                for (a, b) in a1.iter().zip(a2.iter()) {
                    self.mgu(a, b)?;
                }
                Ok(())
            }

            // Everything else fails
            _ => Err(UnifyError::Mismatch),
        }
    }

    /// Try to unify, returning a new substitution on success.
    /// Does not modify self on failure.
    pub fn try_mgu(&self, x: &Term, y: &Term) -> Result<Subst, UnifyError> {
        let mut new_subst = self.clone();
        new_subst.mgu(x, y)?;
        Ok(new_subst)
    }

    /// One-way matching: x covers y (x is more general than y).
    ///
    /// Only binds variables in x, not in y.
    pub fn cover(&mut self, x: &Term, y: &Term) -> Result<(), UnifyError> {
        let x = self.deref(x);
        let y_deref = self.deref(y);

        match (&x, &y_deref) {
            _ if x == y_deref => Ok(()),

            (Term::Var(v), _) => {
                // Only bind variables from x (the pattern)
                self.bindings.insert(*v, y_deref);
                Ok(())
            }

            (
                Term::Compound {
                    functor: f1,
                    args: a1,
                },
                Term::Compound {
                    functor: f2,
                    args: a2,
                },
            ) if f1 == f2 && a1.len() == a2.len() => {
                for (a, b) in a1.iter().zip(a2.iter()) {
                    self.cover(a, b)?;
                }
                Ok(())
            }

            _ => Err(UnifyError::Mismatch),
        }
    }

    /// Try to match, returning a new substitution on success.
    pub fn try_cover(&self, x: &Term, y: &Term) -> Result<Subst, UnifyError> {
        let mut new_subst = self.clone();
        new_subst.cover(x, y)?;
        Ok(new_subst)
    }

    /// Freshen a term by replacing all variables with fresh ones.
    pub fn fresh(&mut self, term: &Term) -> Term {
        let mut var_map: FxHashMap<VarId, VarId> = FxHashMap::default();
        self.fresh_impl(term, &mut var_map)
    }

    fn fresh_impl(&mut self, term: &Term, var_map: &mut FxHashMap<VarId, VarId>) -> Term {
        match term {
            Term::Var(v) => {
                let new_v = *var_map.entry(*v).or_insert_with(|| self.fresh_var());
                Term::Var(new_v)
            }
            Term::Compound { functor, args } => Term::Compound {
                functor: functor.clone(),
                args: args.iter().map(|a| self.fresh_impl(a, var_map)).collect(),
            },
            Term::Const(_) => term.clone(),
        }
    }

    /// Freshen a product.
    pub fn fresh_product(&mut self, product: &Product) -> Product {
        let mut var_map: FxHashMap<VarId, VarId> = FxHashMap::default();
        Product::new(
            product
                .iter()
                .map(|t| self.fresh_impl(t, &mut var_map))
                .collect(),
        )
    }

    /// Canonicalize a term by renumbering variables in order of first occurrence.
    pub fn canonicalize(term: &Term) -> Term {
        let mut var_map: FxHashMap<VarId, VarId> = FxHashMap::default();
        let mut next = 0;
        Self::canonicalize_impl(term, &mut var_map, &mut next)
    }

    fn canonicalize_impl(
        term: &Term,
        var_map: &mut FxHashMap<VarId, VarId>,
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
                args: args
                    .iter()
                    .map(|a| Self::canonicalize_impl(a, var_map, next))
                    .collect(),
            },
            Term::Const(_) => term.clone(),
        }
    }

    /// Canonicalize a product.
    pub fn canonicalize_product(product: &Product) -> Product {
        let mut var_map: FxHashMap<VarId, VarId> = FxHashMap::default();
        let mut next = 0;
        Product::new(
            product
                .iter()
                .map(|t| Self::canonicalize_impl(t, &mut var_map, &mut next))
                .collect(),
        )
    }

    /// Check if this substitution is a variable renaming (bijective on variables).
    pub fn is_renaming(&self) -> bool {
        let mut seen: FxHashMap<VarId, VarId> = FxHashMap::default();
        for (v, term) in &self.bindings {
            match term {
                Term::Var(u) => {
                    if seen.contains_key(u) {
                        return false; // Two vars map to same var
                    }
                    seen.insert(*u, *v);
                }
                _ => return false, // Binding to non-variable
            }
        }
        true
    }

    /// Compose two substitutions: apply self first, then other.
    pub fn compose(&self, other: &Subst) -> Subst {
        let mut result = Subst::with_next_var(self.next_var.max(other.next_var));

        // Apply other to all bindings in self
        for (v, term) in &self.bindings {
            result.bindings.insert(*v, other.deref(term));
        }

        // Add bindings from other that aren't in self
        for (v, term) in &other.bindings {
            if !result.bindings.contains_key(v) {
                result.bindings.insert(*v, term.clone());
            }
        }

        result
    }

    /// Restrict the substitution to only the given variables.
    pub fn restrict(&self, vars: &[VarId]) -> Subst {
        let mut result = Subst::with_next_var(self.next_var);
        for v in vars {
            if let Some(term) = self.bindings.get(v) {
                result.bindings.insert(*v, term.clone());
            }
        }
        result
    }
}

impl fmt::Display for Subst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for (v, term) in &self.bindings {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "_{} -> {}", v, term)?;
            first = false;
        }
        write!(f, "}}")
    }
}

/// Convenience function to unify two terms.
pub fn unify(x: &Term, y: &Term) -> Result<Subst, UnifyError> {
    let mut subst = Subst::new();
    subst.mgu(x, y)?;
    Ok(subst)
}

/// Convenience function to check if x covers (is more general than) y.
pub fn covers(x: &Term, y: &Term) -> Result<Subst, UnifyError> {
    let mut subst = Subst::new();
    subst.cover(x, y)?;
    Ok(subst)
}

/// Check if two terms are equal modulo variable renaming.
pub fn alpha_equivalent(x: &Term, y: &Term) -> bool {
    Subst::canonicalize(x) == Subst::canonicalize(y)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Value;

    #[test]
    fn test_unify_identical() {
        let t1 = Term::compound("f", vec![Term::constant(Value::Int(1))]);
        let t2 = Term::compound("f", vec![Term::constant(Value::Int(1))]);
        assert!(unify(&t1, &t2).is_ok());
    }

    #[test]
    fn test_unify_var_const() {
        let x = Term::var(0);
        let c = Term::constant(Value::Int(42));
        let subst = unify(&x, &c).unwrap();
        assert_eq!(subst.deref(&x), c);
    }

    #[test]
    fn test_unify_vars() {
        let x = Term::var(0);
        let y = Term::var(1);
        let subst = unify(&x, &y).unwrap();
        // After unification, dereferencing both should give same result
        assert_eq!(subst.deref(&x), subst.deref(&y));
    }

    #[test]
    fn test_unify_compound() {
        let t1 = Term::compound("f", vec![Term::var(0), Term::constant(Value::Int(1))]);
        let t2 = Term::compound(
            "f",
            vec![Term::constant(Value::Int(2)), Term::var(1)],
        );
        let subst = unify(&t1, &t2).unwrap();
        assert_eq!(subst.deref(&Term::var(0)), Term::constant(Value::Int(2)));
        assert_eq!(subst.deref(&Term::var(1)), Term::constant(Value::Int(1)));
    }

    #[test]
    fn test_unify_nested() {
        // f(X, g(Y)) = f(a, g(b))
        let t1 = Term::compound(
            "f",
            vec![Term::var(0), Term::compound("g", vec![Term::var(1)])],
        );
        let t2 = Term::compound(
            "f",
            vec![
                Term::atom("a"),
                Term::compound("g", vec![Term::atom("b")]),
            ],
        );
        let subst = unify(&t1, &t2).unwrap();
        assert_eq!(subst.deref(&Term::var(0)), Term::atom("a"));
        assert_eq!(subst.deref(&Term::var(1)), Term::atom("b"));
    }

    #[test]
    fn test_unify_fail_functor() {
        let t1 = Term::compound("f", vec![Term::var(0)]);
        let t2 = Term::compound("g", vec![Term::var(0)]);
        assert!(unify(&t1, &t2).is_err());
    }

    #[test]
    fn test_unify_fail_arity() {
        let t1 = Term::compound("f", vec![Term::var(0)]);
        let t2 = Term::compound("f", vec![Term::var(0), Term::var(1)]);
        assert!(unify(&t1, &t2).is_err());
    }

    #[test]
    fn test_occurs_check() {
        // X = f(X) should fail
        let x = Term::var(0);
        let fx = Term::compound("f", vec![Term::var(0)]);
        assert!(matches!(unify(&x, &fx), Err(UnifyError::OccursCheck)));
    }

    #[test]
    fn test_cover() {
        // f(X, Y) covers f(1, 2)
        let pattern = Term::compound("f", vec![Term::var(0), Term::var(1)]);
        let term = Term::compound(
            "f",
            vec![Term::constant(Value::Int(1)), Term::constant(Value::Int(2))],
        );
        let subst = covers(&pattern, &term).unwrap();
        assert_eq!(subst.deref(&Term::var(0)), Term::constant(Value::Int(1)));
        assert_eq!(subst.deref(&Term::var(1)), Term::constant(Value::Int(2)));
    }

    #[test]
    fn test_cover_fail() {
        // f(1, Y) does not cover f(2, 3)
        let pattern = Term::compound("f", vec![Term::constant(Value::Int(1)), Term::var(1)]);
        let term = Term::compound(
            "f",
            vec![Term::constant(Value::Int(2)), Term::constant(Value::Int(3))],
        );
        assert!(covers(&pattern, &term).is_err());
    }

    #[test]
    fn test_fresh() {
        let mut subst = Subst::with_next_var(10);
        let t = Term::compound("f", vec![Term::var(0), Term::var(1), Term::var(0)]);
        let fresh_t = subst.fresh(&t);

        // Should have new variable IDs
        let vars = fresh_t.vars();
        assert!(!vars.contains(&0));
        assert!(!vars.contains(&1));
        // Both occurrences of var(0) should map to the same new variable
        if let Term::Compound { args, .. } = &fresh_t {
            assert_eq!(args[0], args[2]);
        }
    }

    #[test]
    fn test_canonicalize() {
        // f(Y, X, Y) should become f(_0, _1, _0)
        let t = Term::compound("f", vec![Term::var(5), Term::var(3), Term::var(5)]);
        let canon = Subst::canonicalize(&t);

        if let Term::Compound { args, .. } = &canon {
            assert_eq!(args[0], Term::var(0));
            assert_eq!(args[1], Term::var(1));
            assert_eq!(args[2], Term::var(0));
        }
    }

    #[test]
    fn test_alpha_equivalent() {
        let t1 = Term::compound("f", vec![Term::var(0), Term::var(1)]);
        let t2 = Term::compound("f", vec![Term::var(5), Term::var(10)]);
        assert!(alpha_equivalent(&t1, &t2));

        // f(X, X) is not alpha-equivalent to f(X, Y)
        let t3 = Term::compound("f", vec![Term::var(0), Term::var(0)]);
        let t4 = Term::compound("f", vec![Term::var(0), Term::var(1)]);
        assert!(!alpha_equivalent(&t3, &t4));
    }

    #[test]
    fn test_is_renaming() {
        let mut subst = Subst::new();
        subst.bind(0, Term::var(5));
        subst.bind(1, Term::var(6));
        assert!(subst.is_renaming());

        let mut subst2 = Subst::new();
        subst2.bind(0, Term::constant(Value::Int(1)));
        assert!(!subst2.is_renaming());
    }

    #[test]
    fn test_compose() {
        let mut s1 = Subst::new();
        s1.bind(0, Term::var(1));

        let mut s2 = Subst::new();
        s2.bind(1, Term::constant(Value::Int(42)));

        let composed = s1.compose(&s2);
        assert_eq!(
            composed.deref(&Term::var(0)),
            Term::constant(Value::Int(42))
        );
    }
}
