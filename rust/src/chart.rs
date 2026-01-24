//! Indexed chart for efficient item storage and retrieval.
//!
//! The chart stores item -> value mappings and automatically maintains
//! indexes for efficient query lookups based on bound argument patterns.

use crate::semiring::Semiring;
use crate::subst::Subst;
use crate::term::Term;
use rustc_hash::{FxHashMap, FxHashSet};
use std::rc::Rc;

/// A query mode describes which argument positions are bound (ground) in a query.
pub type Mode = Vec<usize>;

/// A key for index lookup: the ground values at the bound positions.
pub type IndexKey = Vec<Term>;

/// Functor and arity pair.
pub type FunctorArity = (Rc<str>, usize);

/// Index for a single (functor, arity, mode) combination.
#[derive(Debug, Default)]
struct ModeIndex {
    /// Map from key (bound argument values) to set of matching items.
    entries: FxHashMap<IndexKey, FxHashSet<Term>>,
}

impl ModeIndex {
    fn new() -> Self {
        ModeIndex {
            entries: FxHashMap::default(),
        }
    }

    fn insert(&mut self, key: IndexKey, item: Term) {
        self.entries
            .entry(key)
            .or_insert_with(FxHashSet::default)
            .insert(item);
    }

    fn get(&self, key: &IndexKey) -> Option<&FxHashSet<Term>> {
        self.entries.get(key)
    }
}

/// Index structure for a single (functor, arity) combination.
#[derive(Debug, Default)]
struct FunctorIndex {
    /// Map from mode to ModeIndex.
    by_mode: FxHashMap<Mode, ModeIndex>,
}

impl FunctorIndex {
    fn new() -> Self {
        FunctorIndex {
            by_mode: FxHashMap::default(),
        }
    }
}

/// An indexed chart for storing and querying items with semiring values.
#[derive(Debug)]
pub struct Chart<S: Semiring> {
    /// The main item -> value storage.
    items: FxHashMap<Term, S>,

    /// Indexes by (functor, arity).
    indices: FxHashMap<FunctorArity, FunctorIndex>,
}

impl<S: Semiring> Default for Chart<S> {
    fn default() -> Self {
        Self::new()
    }
}

impl<S: Semiring> Chart<S> {
    /// Create a new empty chart.
    pub fn new() -> Self {
        Chart {
            items: FxHashMap::default(),
            indices: FxHashMap::default(),
        }
    }

    /// Get the number of items in the chart.
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Check if the chart is empty.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Get the value for an item, if present.
    pub fn get(&self, item: &Term) -> Option<&S> {
        self.items.get(item)
    }

    /// Check if an item is in the chart.
    pub fn contains(&self, item: &Term) -> bool {
        self.items.contains_key(item)
    }

    /// Insert or update an item's value.
    pub fn insert(&mut self, item: Term, value: S) {
        let is_new = !self.items.contains_key(&item);
        self.items.insert(item.clone(), value);

        if is_new {
            self.update_indices(&item);
        }
    }

    /// Add a delta to an item's value (using semiring addition).
    pub fn add(&mut self, item: Term, delta: S) -> S {
        let is_new = !self.items.contains_key(&item);
        let new_value = self
            .items
            .get(&item)
            .cloned()
            .unwrap_or(S::zero())
            + delta;
        self.items.insert(item.clone(), new_value.clone());

        if is_new {
            self.update_indices(&item);
        }

        new_value
    }

    /// Iterate over all (item, value) pairs.
    pub fn iter(&self) -> impl Iterator<Item = (&Term, &S)> {
        self.items.iter()
    }

    /// Query the chart for items matching a pattern.
    ///
    /// Returns an iterator over (item, value, substitution) triples where
    /// the substitution unifies the pattern with the item.
    pub fn query<'a>(&'a mut self, pattern: &'a Term) -> QueryResult<'a, S> {
        let (fa, mode, key) = Self::analyze_query(pattern);

        // Ensure the index exists for this mode
        self.ensure_index(&fa, &mode);

        // Get matching candidates from the index
        let candidates: Vec<Term> = self
            .indices
            .get(&fa)
            .and_then(|fi| fi.by_mode.get(&mode))
            .and_then(|mi| mi.get(&key))
            .map(|set| set.iter().cloned().collect())
            .unwrap_or_default();

        QueryResult {
            chart: self,
            pattern: pattern.clone(),
            candidates,
            index: 0,
        }
    }

    /// Simple linear scan query (no indexing, for comparison/fallback).
    pub fn query_linear<'a>(&'a self, pattern: &'a Term) -> impl Iterator<Item = (&'a Term, &'a S, Subst)> {
        let pattern_clone = pattern.clone();
        self.items.iter().filter_map(move |(item, value)| {
            let mut subst = Subst::new();
            if subst.mgu(&pattern_clone, item).is_ok() {
                Some((item, value, subst))
            } else {
                None
            }
        })
    }

    /// Analyze a query pattern to determine the mode and key.
    fn analyze_query(pattern: &Term) -> (FunctorArity, Mode, IndexKey) {
        match pattern {
            Term::Compound { functor, args } => {
                let fa = (functor.clone(), args.len());
                let mut mode = Vec::new();
                let mut key = Vec::new();

                for (i, arg) in args.iter().enumerate() {
                    if arg.is_ground() {
                        mode.push(i);
                        key.push(arg.clone());
                    }
                }

                (fa, mode, key)
            }
            _ => {
                // Non-compound terms: use empty functor
                let fa: FunctorArity = ("".into(), 0);
                (fa, Vec::new(), Vec::new())
            }
        }
    }

    /// Ensure an index exists for the given (functor, arity, mode) combination.
    fn ensure_index(&mut self, fa: &FunctorArity, mode: &Mode) {
        let fi = self
            .indices
            .entry(fa.clone())
            .or_insert_with(FunctorIndex::new);

        if !fi.by_mode.contains_key(mode) {
            // Build the index by scanning existing items
            let mut mode_index = ModeIndex::new();

            for item in self.items.keys() {
                if let Term::Compound { functor, args } = item {
                    if functor == &fa.0 && args.len() == fa.1 {
                        let key: IndexKey = mode.iter().map(|&i| args[i].clone()).collect();
                        mode_index.insert(key, item.clone());
                    }
                }
            }

            fi.by_mode.insert(mode.clone(), mode_index);
        }
    }

    /// Update all existing indexes when a new item is added.
    fn update_indices(&mut self, item: &Term) {
        if let Term::Compound { functor, args } = item {
            let fa = (functor.clone(), args.len());

            if let Some(fi) = self.indices.get_mut(&fa) {
                for (mode, mode_index) in &mut fi.by_mode {
                    let key: IndexKey = mode.iter().map(|&i| args[i].clone()).collect();
                    mode_index.insert(key, item.clone());
                }
            }
        }
    }

    /// Get statistics about the indexes.
    pub fn index_stats(&self) -> IndexStats {
        let mut num_indexes = 0;
        let mut total_entries = 0;

        for fi in self.indices.values() {
            for mi in fi.by_mode.values() {
                num_indexes += 1;
                total_entries += mi.entries.len();
            }
        }

        IndexStats {
            num_items: self.items.len(),
            num_indexes,
            total_entries,
        }
    }
}

/// Statistics about chart indexes.
#[derive(Debug, Clone)]
pub struct IndexStats {
    pub num_items: usize,
    pub num_indexes: usize,
    pub total_entries: usize,
}

/// Iterator over query results.
pub struct QueryResult<'a, S: Semiring> {
    chart: &'a Chart<S>,
    pattern: Term,
    candidates: Vec<Term>,
    index: usize,
}

impl<'a, S: Semiring> Iterator for QueryResult<'a, S> {
    type Item = (Term, S, Subst);

    fn next(&mut self) -> Option<Self::Item> {
        while self.index < self.candidates.len() {
            let item = &self.candidates[self.index];
            self.index += 1;

            let mut subst = Subst::new();
            if subst.mgu(&self.pattern, item).is_ok() {
                if let Some(value) = self.chart.items.get(item) {
                    return Some((item.clone(), value.clone(), subst));
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semiring::Float;
    use crate::term::Value;

    #[test]
    fn test_chart_insert_get() {
        let mut chart: Chart<Float> = Chart::new();

        let item = Term::compound("f", vec![Term::constant(Value::Int(1))]);
        chart.insert(item.clone(), Float::new(0.5));

        assert!(chart.contains(&item));
        assert_eq!(chart.get(&item), Some(&Float::new(0.5)));
    }

    #[test]
    fn test_chart_add() {
        let mut chart: Chart<Float> = Chart::new();

        let item = Term::compound("f", vec![Term::constant(Value::Int(1))]);
        chart.add(item.clone(), Float::new(0.3));
        chart.add(item.clone(), Float::new(0.2));

        assert_eq!(chart.get(&item), Some(&Float::new(0.5)));
    }

    #[test]
    fn test_chart_query() {
        let mut chart: Chart<Float> = Chart::new();

        // Add some items
        chart.insert(
            Term::compound(
                "edge",
                vec![Term::constant(Value::Int(1)), Term::constant(Value::Int(2))],
            ),
            Float::new(1.0),
        );
        chart.insert(
            Term::compound(
                "edge",
                vec![Term::constant(Value::Int(1)), Term::constant(Value::Int(3))],
            ),
            Float::new(2.0),
        );
        chart.insert(
            Term::compound(
                "edge",
                vec![Term::constant(Value::Int(2)), Term::constant(Value::Int(3))],
            ),
            Float::new(3.0),
        );

        // Query for edges starting from node 1
        let pattern = Term::compound(
            "edge",
            vec![Term::constant(Value::Int(1)), Term::var(0)],
        );

        let results: Vec<_> = chart.query(&pattern).collect();
        assert_eq!(results.len(), 2);

        // Check that we got the right values
        let values: FxHashSet<_> = results.iter().map(|(_, v, _)| (v.0 * 10.0) as i32).collect();
        assert!(values.contains(&10)); // 1.0
        assert!(values.contains(&20)); // 2.0
    }

    #[test]
    fn test_chart_query_all_bound() {
        let mut chart: Chart<Float> = Chart::new();

        let item = Term::compound(
            "f",
            vec![Term::constant(Value::Int(1)), Term::constant(Value::Int(2))],
        );
        chart.insert(item.clone(), Float::new(0.5));

        // Query with all arguments bound
        let results: Vec<_> = chart.query(&item).collect();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].1, Float::new(0.5));
    }

    #[test]
    fn test_chart_query_all_free() {
        let mut chart: Chart<Float> = Chart::new();

        chart.insert(
            Term::compound(
                "f",
                vec![Term::constant(Value::Int(1)), Term::constant(Value::Int(2))],
            ),
            Float::new(1.0),
        );
        chart.insert(
            Term::compound(
                "f",
                vec![Term::constant(Value::Int(3)), Term::constant(Value::Int(4))],
            ),
            Float::new(2.0),
        );

        // Query with all arguments free
        let pattern = Term::compound("f", vec![Term::var(0), Term::var(1)]);
        let results: Vec<_> = chart.query(&pattern).collect();
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn test_chart_linear_query() {
        let mut chart: Chart<Float> = Chart::new();

        chart.insert(
            Term::compound(
                "edge",
                vec![Term::constant(Value::Int(1)), Term::constant(Value::Int(2))],
            ),
            Float::new(1.0),
        );

        let pattern = Term::compound(
            "edge",
            vec![Term::constant(Value::Int(1)), Term::var(0)],
        );

        let results: Vec<_> = chart.query_linear(&pattern).collect();
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn test_index_stats() {
        let mut chart: Chart<Float> = Chart::new();

        chart.insert(
            Term::compound("f", vec![Term::constant(Value::Int(1))]),
            Float::new(1.0),
        );

        // Trigger index creation
        let pattern = Term::compound("f", vec![Term::constant(Value::Int(1))]);
        let _ = chart.query(&pattern).collect::<Vec<_>>();

        let stats = chart.index_stats();
        assert_eq!(stats.num_items, 1);
        assert!(stats.num_indexes >= 1);
    }
}
