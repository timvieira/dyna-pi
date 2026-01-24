//! String interning and hash consing for terms.
//!
//! This module provides efficient term representation through:
//! 1. String interning: Map strings to integer IDs for O(1) comparison
//! 2. Hash consing: Share identical term structures

use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::hash::{Hash, Hasher};

/// Interned symbol ID - replaces Rc<str> for O(1) comparison
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymbolId(u32);

impl SymbolId {
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

/// Global symbol table for string interning
///
/// Thread-local for safety without locks. In a multi-threaded context,
/// you'd want a concurrent hash map or arena allocation.
#[derive(Debug, Default)]
pub struct SymbolTable {
    str_to_id: FxHashMap<Box<str>, SymbolId>,
    id_to_str: Vec<Box<str>>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern a string, returning its unique ID
    pub fn intern(&mut self, s: &str) -> SymbolId {
        if let Some(&id) = self.str_to_id.get(s) {
            return id;
        }

        let id = SymbolId(self.id_to_str.len() as u32);
        let boxed: Box<str> = s.into();
        self.str_to_id.insert(boxed.clone(), id);
        self.id_to_str.push(boxed);
        id
    }

    /// Look up the string for an ID
    pub fn resolve(&self, id: SymbolId) -> &str {
        &self.id_to_str[id.0 as usize]
    }

    /// Number of interned symbols
    pub fn len(&self) -> usize {
        self.id_to_str.len()
    }

    pub fn is_empty(&self) -> bool {
        self.id_to_str.is_empty()
    }
}

// Thread-local symbol table for convenience
thread_local! {
    static SYMBOLS: RefCell<SymbolTable> = RefCell::new(SymbolTable::new());
}

/// Intern a string using the thread-local symbol table
pub fn intern(s: &str) -> SymbolId {
    SYMBOLS.with(|table| table.borrow_mut().intern(s))
}

/// Resolve a symbol ID to its string
pub fn resolve(id: SymbolId) -> String {
    SYMBOLS.with(|table| table.borrow().resolve(id).to_string())
}

/// Reset the thread-local symbol table (useful for testing)
pub fn reset_symbols() {
    SYMBOLS.with(|table| *table.borrow_mut() = SymbolTable::new());
}

// ============================================================================
// Interned Term - Optimized term representation
// ============================================================================

/// Variable ID (same as before)
pub type VarId = u32;

/// Optimized value representation
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum IValue {
    Int(i64),
    Symbol(SymbolId),  // Interned symbol instead of Rc<str>
}

/// Optimized term with interned functors
///
/// Key differences from Term:
/// - Functor is SymbolId (u32) instead of Rc<str>
/// - Comparison is O(1) for functors
/// - Hashing is much faster
#[derive(Clone, Debug)]
pub enum ITerm {
    Var(VarId),
    Const(IValue),
    Compound {
        functor: SymbolId,
        args: Vec<ITerm>,
    },
}

impl ITerm {
    pub fn var(id: VarId) -> Self {
        ITerm::Var(id)
    }

    pub fn int(n: i64) -> Self {
        ITerm::Const(IValue::Int(n))
    }

    pub fn symbol(s: &str) -> Self {
        ITerm::Const(IValue::Symbol(intern(s)))
    }

    pub fn compound(functor: &str, args: Vec<ITerm>) -> Self {
        ITerm::Compound {
            functor: intern(functor),
            args,
        }
    }

    pub fn atom(name: &str) -> Self {
        ITerm::Compound {
            functor: intern(name),
            args: Vec::new(),
        }
    }

    pub fn functor(&self) -> Option<SymbolId> {
        match self {
            ITerm::Compound { functor, .. } => Some(*functor),
            _ => None,
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            ITerm::Compound { args, .. } => args.len(),
            _ => 0,
        }
    }

    pub fn functor_arity(&self) -> Option<(SymbolId, usize)> {
        match self {
            ITerm::Compound { functor, args } => Some((*functor, args.len())),
            _ => None,
        }
    }

    pub fn is_ground(&self) -> bool {
        match self {
            ITerm::Var(_) => false,
            ITerm::Const(_) => true,
            ITerm::Compound { args, .. } => args.iter().all(|a| a.is_ground()),
        }
    }

    pub fn is_var(&self) -> bool {
        matches!(self, ITerm::Var(_))
    }

    pub fn args(&self) -> Option<&[ITerm]> {
        match self {
            ITerm::Compound { args, .. } => Some(args),
            _ => None,
        }
    }
}

impl PartialEq for ITerm {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ITerm::Var(a), ITerm::Var(b)) => a == b,
            (ITerm::Const(a), ITerm::Const(b)) => a == b,
            (
                ITerm::Compound { functor: f1, args: a1 },
                ITerm::Compound { functor: f2, args: a2 },
            ) => {
                // Functor comparison is now O(1) - just compare u32s!
                f1 == f2 && a1.len() == a2.len() && a1 == a2
            }
            _ => false,
        }
    }
}

impl Eq for ITerm {}

impl Hash for ITerm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            ITerm::Var(v) => v.hash(state),
            ITerm::Const(c) => c.hash(state),
            ITerm::Compound { functor, args } => {
                // Just hash the u32 functor ID - much faster than string hashing!
                functor.hash(state);
                args.len().hash(state);
                for arg in args {
                    arg.hash(state);
                }
            }
        }
    }
}

impl std::fmt::Display for ITerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ITerm::Var(v) => write!(f, "_{}", v),
            ITerm::Const(IValue::Int(n)) => write!(f, "{}", n),
            ITerm::Const(IValue::Symbol(s)) => write!(f, "{}", resolve(*s)),
            ITerm::Compound { functor, args } if args.is_empty() => {
                write!(f, "{}", resolve(*functor))
            }
            ITerm::Compound { functor, args } => {
                write!(f, "{}(", resolve(*functor))?;
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

// ============================================================================
// Hash Consing for Terms
// ============================================================================

/// A hash-consed term reference
///
/// With hash consing, identical terms share the same allocation.
/// This enables O(1) equality via pointer comparison.
#[derive(Clone)]
pub struct HcTerm(std::rc::Rc<HcTermInner>);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum HcTermInner {
    Var(VarId),
    Int(i64),
    Symbol(SymbolId),
    Compound {
        functor: SymbolId,
        args: Vec<HcTerm>,
    },
}

impl PartialEq for HcTerm {
    fn eq(&self, other: &Self) -> bool {
        // O(1) pointer comparison!
        std::rc::Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for HcTerm {}

impl Hash for HcTerm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash the pointer address - O(1)!
        std::rc::Rc::as_ptr(&self.0).hash(state);
    }
}

/// Hash cons table for term interning
#[derive(Default)]
pub struct HcTable {
    table: FxHashMap<HcTermInner, std::rc::Rc<HcTermInner>>,
}

impl HcTable {
    pub fn new() -> Self {
        Self::default()
    }

    fn intern(&mut self, inner: HcTermInner) -> HcTerm {
        if let Some(existing) = self.table.get(&inner) {
            return HcTerm(existing.clone());
        }

        let rc = std::rc::Rc::new(inner.clone());
        self.table.insert(inner, rc.clone());
        HcTerm(rc)
    }

    pub fn var(&mut self, id: VarId) -> HcTerm {
        self.intern(HcTermInner::Var(id))
    }

    pub fn int(&mut self, n: i64) -> HcTerm {
        self.intern(HcTermInner::Int(n))
    }

    pub fn symbol(&mut self, s: &str) -> HcTerm {
        self.intern(HcTermInner::Symbol(intern(s)))
    }

    pub fn compound(&mut self, functor: &str, args: Vec<HcTerm>) -> HcTerm {
        self.intern(HcTermInner::Compound {
            functor: intern(functor),
            args,
        })
    }

    pub fn atom(&mut self, name: &str) -> HcTerm {
        self.compound(name, Vec::new())
    }

    pub fn len(&self) -> usize {
        self.table.len()
    }
}

impl HcTerm {
    pub fn is_ground(&self) -> bool {
        match &*self.0 {
            HcTermInner::Var(_) => false,
            HcTermInner::Int(_) | HcTermInner::Symbol(_) => true,
            HcTermInner::Compound { args, .. } => args.iter().all(|a| a.is_ground()),
        }
    }

    pub fn is_var(&self) -> bool {
        matches!(&*self.0, HcTermInner::Var(_))
    }

    pub fn functor_arity(&self) -> Option<(SymbolId, usize)> {
        match &*self.0 {
            HcTermInner::Compound { functor, args } => Some((*functor, args.len())),
            _ => None,
        }
    }
}

impl std::fmt::Debug for HcTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl std::fmt::Display for HcTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &*self.0 {
            HcTermInner::Var(v) => write!(f, "_{}", v),
            HcTermInner::Int(n) => write!(f, "{}", n),
            HcTermInner::Symbol(s) => write!(f, "{}", resolve(*s)),
            HcTermInner::Compound { functor, args } if args.is_empty() => {
                write!(f, "{}", resolve(*functor))
            }
            HcTermInner::Compound { functor, args } => {
                write!(f, "{}(", resolve(*functor))?;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_symbol_interning() {
        reset_symbols();

        let id1 = intern("foo");
        let id2 = intern("bar");
        let id3 = intern("foo");

        assert_eq!(id1, id3);  // Same string -> same ID
        assert_ne!(id1, id2);  // Different strings -> different IDs

        assert_eq!(resolve(id1), "foo");
        assert_eq!(resolve(id2), "bar");
    }

    #[test]
    fn test_iterm_equality() {
        reset_symbols();

        let t1 = ITerm::compound("f", vec![ITerm::int(1), ITerm::int(2)]);
        let t2 = ITerm::compound("f", vec![ITerm::int(1), ITerm::int(2)]);
        let t3 = ITerm::compound("f", vec![ITerm::int(1), ITerm::int(3)]);

        assert_eq!(t1, t2);
        assert_ne!(t1, t3);
    }

    #[test]
    fn test_hash_consing() {
        reset_symbols();

        let mut hc = HcTable::new();

        // Build terms by extracting intermediate values first
        let int1 = hc.int(1);
        let int2 = hc.int(2);
        let t1 = hc.compound("f", vec![int1, int2]);

        let int1 = hc.int(1);
        let int2 = hc.int(2);
        let t2 = hc.compound("f", vec![int1, int2]);

        // Pointer equality - O(1)!
        assert_eq!(t1, t2);
        assert!(std::rc::Rc::ptr_eq(&t1.0, &t2.0));

        // Different terms are different
        let int1 = hc.int(1);
        let int3 = hc.int(3);
        let t3 = hc.compound("f", vec![int1, int3]);
        assert_ne!(t1, t3);
    }

    #[test]
    fn test_hash_consing_sharing() {
        reset_symbols();

        let mut hc = HcTable::new();

        // Build nested term
        let int1 = hc.int(1);
        let inner = hc.compound("g", vec![int1]);
        let t1 = hc.compound("f", vec![inner.clone(), inner.clone()]);

        // The inner terms share the same allocation
        if let HcTermInner::Compound { args, .. } = &*t1.0 {
            assert!(std::rc::Rc::ptr_eq(&args[0].0, &args[1].0));
        }
    }
}
