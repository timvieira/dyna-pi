//! Dyna-Rust: High-performance Rust implementation of Dyna term library and solver.
//!
//! This crate provides:
//! - Term representation (variables, constants, compound terms)
//! - Substitution and unification
//! - Rules and programs
//! - Indexed chart for efficient lookups
//! - Forward chaining solver
//! - Python bindings via PyO3

pub mod chart;
pub mod rule;
pub mod semiring;
pub mod solver;
pub mod subst;
pub mod term;

// Re-exports for convenience
pub use chart::Chart;
pub use rule::{Program, Rule};
pub use semiring::{Boolean, Count, Float, MaxTimes, MinPlus, Semiring};
pub use solver::{Solver, SolverBuilder, SolverConfig, SolverStats};
pub use subst::{covers, unify, Subst, UnifyError};
pub use term::{Product, Term, Value, VarId};

// Python bindings
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyTuple};

/// Convert a Python object to a Rust Term.
fn py_to_term(py: Python, obj: &PyAny) -> PyResult<Term> {
    // Check if it's a tuple (compound term representation)
    if let Ok(tuple) = obj.downcast::<PyTuple>() {
        if tuple.is_empty() {
            return Err(PyValueError::new_err("Empty tuple cannot be a term"));
        }

        let first = tuple.get_item(0)?;

        // Check if first element is a string (functor)
        if let Ok(functor) = first.extract::<String>() {
            let args: Vec<Term> = tuple
                .iter()
                .skip(1)
                .map(|item| py_to_term(py, item))
                .collect::<PyResult<_>>()?;
            return Ok(Term::compound(functor, args));
        }
    }

    // Check for int
    if let Ok(n) = obj.extract::<i64>() {
        return Ok(Term::constant(Value::Int(n)));
    }

    // Check for float
    if let Ok(f) = obj.extract::<f64>() {
        return Ok(Term::constant(Value::Float(ordered_float::OrderedFloat(f))));
    }

    // Check for bool
    if let Ok(b) = obj.extract::<bool>() {
        return Ok(Term::constant(Value::Bool(b)));
    }

    // Check for string
    if let Ok(s) = obj.extract::<String>() {
        // Strings starting with uppercase or _ are variables
        if s.starts_with('_') || s.chars().next().map_or(false, |c| c.is_uppercase()) {
            // Parse variable ID from name like "_0" or "X"
            let var_id = if s.starts_with('_') {
                s[1..].parse::<VarId>().unwrap_or(0)
            } else {
                // Map variable names to IDs
                s.chars().next().map_or(0, |c| c as VarId - 'A' as VarId)
            };
            return Ok(Term::var(var_id));
        } else {
            // Atom/symbol
            return Ok(Term::atom(s));
        }
    }

    Err(PyValueError::new_err(format!(
        "Cannot convert {} to Term",
        obj.get_type().name()?
    )))
}

/// Convert a Rust Term to a Python object.
fn term_to_py(py: Python, term: &Term) -> PyObject {
    match term {
        Term::Var(v) => format!("_{}", v).into_py(py),
        Term::Const(Value::Int(n)) => n.into_py(py),
        Term::Const(Value::Float(f)) => f.into_inner().into_py(py),
        Term::Const(Value::Bool(b)) => b.into_py(py),
        Term::Const(Value::Str(s)) => s.as_ref().into_py(py),
        Term::Const(Value::Symbol(s)) => s.as_ref().into_py(py),
        Term::Compound { functor, args } => {
            let py_args: Vec<PyObject> = std::iter::once(functor.as_ref().into_py(py))
                .chain(args.iter().map(|a| term_to_py(py, a)))
                .collect();
            PyTuple::new(py, py_args).into_py(py)
        }
    }
}

/// Python wrapper for Term.
#[pyclass(name = "Term", unsendable)]
#[derive(Clone)]
struct PyTerm {
    inner: Term,
}

#[pymethods]
impl PyTerm {
    #[new]
    #[pyo3(signature = (functor, *args))]
    fn new(py: Python, functor: &str, args: &PyTuple) -> PyResult<Self> {
        let rust_args: Vec<Term> = args
            .iter()
            .map(|a| {
                if let Ok(t) = a.extract::<PyTerm>() {
                    Ok(t.inner)
                } else {
                    py_to_term(py, a)
                }
            })
            .collect::<PyResult<_>>()?;

        Ok(PyTerm {
            inner: Term::compound(functor, rust_args),
        })
    }

    /// Create a variable term.
    #[staticmethod]
    fn var(id: VarId) -> Self {
        PyTerm {
            inner: Term::var(id),
        }
    }

    /// Create an integer constant term.
    #[staticmethod]
    fn int(n: i64) -> Self {
        PyTerm {
            inner: Term::constant(Value::Int(n)),
        }
    }

    /// Create a float constant term.
    #[staticmethod]
    fn float(f: f64) -> Self {
        PyTerm {
            inner: Term::constant(Value::Float(ordered_float::OrderedFloat(f))),
        }
    }

    /// Create an atom (0-arity compound term).
    #[staticmethod]
    fn atom(name: &str) -> Self {
        PyTerm {
            inner: Term::atom(name),
        }
    }

    /// Get the functor name.
    #[getter]
    fn functor(&self) -> Option<String> {
        self.inner.functor().map(|s| s.to_string())
    }

    /// Get the arity.
    #[getter]
    fn arity(&self) -> usize {
        self.inner.arity()
    }

    /// Check if this term is ground.
    fn is_ground(&self) -> bool {
        self.inner.is_ground()
    }

    /// Check if this term is a variable.
    fn is_var(&self) -> bool {
        self.inner.is_var()
    }

    /// Get the arguments as a list.
    fn args(&self, py: Python) -> PyObject {
        match &self.inner {
            Term::Compound { args, .. } => {
                let py_args: Vec<PyObject> = args.iter().map(|a| term_to_py(py, a)).collect();
                PyList::new(py, py_args).into_py(py)
            }
            _ => PyList::empty(py).into_py(py),
        }
    }

    fn __repr__(&self) -> String {
        format!("{}", self.inner)
    }

    fn __str__(&self) -> String {
        format!("{}", self.inner)
    }

    fn __hash__(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.inner.hash(&mut hasher);
        hasher.finish()
    }

    fn __eq__(&self, other: &PyTerm) -> bool {
        self.inner == other.inner
    }
}

/// Python wrapper for Subst.
#[pyclass(name = "Subst", unsendable)]
#[derive(Clone)]
struct PySubst {
    inner: Subst,
}

#[pymethods]
impl PySubst {
    #[new]
    fn new() -> Self {
        PySubst {
            inner: Subst::new(),
        }
    }

    /// Apply the substitution to a term.
    fn apply(&self, term: &PyTerm) -> PyTerm {
        PyTerm {
            inner: self.inner.apply(&term.inner),
        }
    }

    /// Get a binding.
    fn get(&self, var: VarId, py: Python) -> Option<PyObject> {
        self.inner.get(var).map(|t| term_to_py(py, t))
    }

    /// Get all bindings as a dict.
    fn bindings(&self, py: Python) -> PyResult<PyObject> {
        let dict = PyDict::new(py);
        for (v, t) in self.inner.iter() {
            dict.set_item(format!("_{}", v), term_to_py(py, t))?;
        }
        Ok(dict.into_py(py))
    }

    fn __repr__(&self) -> String {
        format!("{}", self.inner)
    }

    fn __len__(&self) -> usize {
        self.inner.len()
    }
}

/// Python wrapper for Rule.
#[pyclass(name = "Rule", unsendable)]
#[derive(Clone)]
struct PyRule {
    inner: Rule,
}

#[pymethods]
impl PyRule {
    #[new]
    fn new(head: &PyTerm, body: Vec<PyTerm>) -> Self {
        let body_terms: Vec<Term> = body.into_iter().map(|t| t.inner).collect();
        PyRule {
            inner: Rule::new(head.inner.clone(), Product::new(body_terms)),
        }
    }

    /// Create a fact (rule with empty body).
    #[staticmethod]
    fn fact(head: &PyTerm) -> Self {
        PyRule {
            inner: Rule::fact(head.inner.clone()),
        }
    }

    /// Get the head.
    #[getter]
    fn head(&self) -> PyTerm {
        PyTerm {
            inner: self.inner.head.clone(),
        }
    }

    /// Get the body as a list of terms.
    fn body(&self) -> Vec<PyTerm> {
        self.inner
            .body
            .iter()
            .map(|t| PyTerm { inner: t.clone() })
            .collect()
    }

    /// Check if this is a fact.
    fn is_fact(&self) -> bool {
        self.inner.is_fact()
    }

    fn __repr__(&self) -> String {
        format!("{}", self.inner)
    }
}

/// Python wrapper for Solver.
#[pyclass(name = "Solver", unsendable)]
struct PySolver {
    inner: Solver<Float>,
}

#[pymethods]
impl PySolver {
    #[new]
    fn new(rules: Vec<PyRule>) -> Self {
        let program = Program::from_rules(rules.into_iter().map(|r| r.inner).collect());
        PySolver {
            inner: Solver::new(program),
        }
    }

    /// Add a fact with a value.
    fn update(&mut self, item: &PyTerm, value: f64) {
        self.inner.update(item.inner.clone(), Float::new(value));
    }

    /// Run forward chaining to fixpoint.
    fn solve(&mut self) {
        self.inner.solve();
    }

    /// Lookup a specific item's value.
    fn lookup(&self, item: &PyTerm) -> Option<f64> {
        self.inner.lookup(&item.inner).map(|v| v.0)
    }

    /// Query for items matching a pattern.
    fn query(&mut self, pattern: &PyTerm, py: Python) -> PyObject {
        let results = self.inner.query(&pattern.inner);
        let py_results: Vec<PyObject> = results.iter().map(|(term, value)| {
            let py_term = term_to_py(py, term);
            let py_value = value.0.into_py(py);
            PyTuple::new(py, vec![py_term, py_value]).into_py(py)
        }).collect();
        PyList::new(py, py_results).into_py(py)
    }

    /// Get the number of items in the chart.
    fn chart_size(&self) -> usize {
        self.inner.chart().len()
    }

    /// Get solver statistics.
    fn stats(&self, py: Python) -> PyResult<PyObject> {
        let stats = self.inner.stats();
        let dict = PyDict::new(py);
        dict.set_item("iterations", stats.iterations)?;
        dict.set_item("updates", stats.updates)?;
        dict.set_item("rule_firings", stats.rule_firings)?;
        dict.set_item("chart_size", stats.chart_size)?;
        Ok(dict.into_py(py))
    }
}

/// Unify two terms.
#[pyfunction]
fn py_unify(x: &PyTerm, y: &PyTerm) -> PyResult<Option<PySubst>> {
    match unify(&x.inner, &y.inner) {
        Ok(subst) => Ok(Some(PySubst { inner: subst })),
        Err(_) => Ok(None),
    }
}

/// Check if x covers (is more general than) y.
#[pyfunction]
fn py_covers(x: &PyTerm, y: &PyTerm) -> PyResult<Option<PySubst>> {
    match covers(&x.inner, &y.inner) {
        Ok(subst) => Ok(Some(PySubst { inner: subst })),
        Err(_) => Ok(None),
    }
}

/// Canonicalize a term (renumber variables in order of occurrence).
#[pyfunction]
fn canonicalize(term: &PyTerm) -> PyTerm {
    PyTerm {
        inner: Subst::canonicalize(&term.inner),
    }
}

/// Check if two terms are alpha-equivalent (equal up to variable renaming).
#[pyfunction]
fn alpha_equivalent(x: &PyTerm, y: &PyTerm) -> bool {
    subst::alpha_equivalent(&x.inner, &y.inner)
}

/// Python module definition.
#[pymodule]
fn dyna_rust(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<PyTerm>()?;
    m.add_class::<PySubst>()?;
    m.add_class::<PyRule>()?;
    m.add_class::<PySolver>()?;
    m.add_function(wrap_pyfunction!(py_unify, m)?)?;
    m.add_function(wrap_pyfunction!(py_covers, m)?)?;
    m.add_function(wrap_pyfunction!(canonicalize, m)?)?;
    m.add_function(wrap_pyfunction!(alpha_equivalent, m)?)?;
    Ok(())
}
