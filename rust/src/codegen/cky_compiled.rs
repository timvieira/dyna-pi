//! Compiled CKY Parser - Hand-optimized reference implementation
//!
//! This module demonstrates what a code generator would produce for CKY parsing.
//! Key optimizations over the generic solver:
//!
//! 1. **Specialized Term Struct**: `Phrase` is a 6-byte struct (2 bytes each for cat, i, j)
//! 2. **Array-Based Indexes**: Direct array indexing instead of hash lookups
//! 3. **No Unification**: Direct field access and comparison
//! 4. **No Substitutions**: Variables are eliminated at compile time
//! 5. **Inlined Semiring**: Values are f64, operations are direct
//!
//! Compared to generic solver:
//! - Term: 6 bytes vs ~48 bytes (8x smaller)
//! - Equality: 1 instruction vs hash + strcmp
//! - Index lookup: O(1) array access vs O(1) hash with higher constant
//! - Rule firing: ~10 instructions vs ~100 instructions

use rustc_hash::FxHashMap;

/// Category ID - interned symbol
pub type CatId = u16;

/// Position in sentence
pub type Pos = u16;

/// A phrase (chart item) - only 6 bytes!
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(C)]
pub struct Phrase {
    pub cat: CatId,
    pub start: Pos,
    pub end: Pos,
}

impl Phrase {
    #[inline(always)]
    pub fn new(cat: CatId, start: Pos, end: Pos) -> Self {
        Phrase { cat, start, end }
    }

    #[inline(always)]
    pub fn span(&self) -> usize {
        (self.end - self.start) as usize
    }
}

/// Rewrite table for binary rules: maps (left_cat, right_cat) -> [parent_cats]
#[derive(Clone, Debug)]
pub struct BinaryRewrites {
    /// rewrites[left][right] = Vec<parent_cat>
    table: Vec<Vec<Vec<CatId>>>,
    num_cats: usize,
}

impl BinaryRewrites {
    pub fn new(num_cats: usize) -> Self {
        BinaryRewrites {
            table: vec![vec![Vec::new(); num_cats]; num_cats],
            num_cats,
        }
    }

    #[inline(always)]
    pub fn add(&mut self, parent: CatId, left: CatId, right: CatId) {
        self.table[left as usize][right as usize].push(parent);
    }

    #[inline(always)]
    pub fn lookup(&self, left: CatId, right: CatId) -> &[CatId] {
        &self.table[left as usize][right as usize]
    }
}

/// Rewrite table for unary/lexical rules: maps word -> [(cat, prob)]
#[derive(Clone, Debug)]
pub struct LexicalRewrites {
    /// word_id -> Vec<(cat, prob)>
    table: FxHashMap<u32, Vec<(CatId, f64)>>,
}

impl LexicalRewrites {
    pub fn new() -> Self {
        LexicalRewrites {
            table: FxHashMap::default(),
        }
    }

    pub fn add(&mut self, word_id: u32, cat: CatId, prob: f64) {
        self.table.entry(word_id).or_default().push((cat, prob));
    }

    #[inline(always)]
    pub fn lookup(&self, word_id: u32) -> &[(CatId, f64)] {
        self.table.get(&word_id).map(|v| v.as_slice()).unwrap_or(&[])
    }
}

impl Default for LexicalRewrites {
    fn default() -> Self {
        Self::new()
    }
}

/// Compiled chart with specialized indexes
#[derive(Clone, Debug)]
pub struct CompiledChart {
    /// Main storage: chart[phrase] = value
    values: FxHashMap<Phrase, f64>,

    /// Index by start position: by_start[i] = phrases starting at i
    by_start: Vec<Vec<Phrase>>,

    /// Index by end position: by_end[j] = phrases ending at j
    by_end: Vec<Vec<Phrase>>,

    /// Index by span: by_span[i][j] = phrases from i to j
    by_span: Vec<Vec<Vec<Phrase>>>,

    /// Sentence length
    n: usize,
}

impl CompiledChart {
    pub fn new(n: usize) -> Self {
        CompiledChart {
            values: FxHashMap::default(),
            by_start: vec![Vec::new(); n + 1],
            by_end: vec![Vec::new(); n + 1],
            by_span: vec![vec![Vec::new(); n + 1]; n + 1],
            n,
        }
    }

    #[inline(always)]
    pub fn insert(&mut self, phrase: Phrase, value: f64) -> bool {
        let is_new = !self.values.contains_key(&phrase);

        // Update or insert value
        let entry = self.values.entry(phrase).or_insert(0.0);
        *entry += value;

        // Update indexes only for new phrases
        if is_new {
            let i = phrase.start as usize;
            let j = phrase.end as usize;
            self.by_start[i].push(phrase);
            self.by_end[j].push(phrase);
            self.by_span[i][j].push(phrase);
        }

        is_new
    }

    #[inline(always)]
    pub fn get(&self, phrase: &Phrase) -> Option<f64> {
        self.values.get(phrase).copied()
    }

    #[inline(always)]
    pub fn starting_at(&self, i: Pos) -> &[Phrase] {
        &self.by_start[i as usize]
    }

    #[inline(always)]
    pub fn ending_at(&self, j: Pos) -> &[Phrase] {
        &self.by_end[j as usize]
    }

    #[inline(always)]
    pub fn spanning(&self, i: Pos, j: Pos) -> &[Phrase] {
        &self.by_span[i as usize][j as usize]
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
}

/// Compiled CKY solver
pub struct CompiledCKY {
    /// Binary grammar rules
    binary_rewrites: BinaryRewrites,
    /// Lexical rules
    lexical_rewrites: LexicalRewrites,
    /// Symbol table: name -> id
    symbols: FxHashMap<String, CatId>,
    /// Reverse symbol table: id -> name
    symbol_names: Vec<String>,
    /// Word table: word -> id
    words: FxHashMap<String, u32>,
    /// Goal category
    goal_cat: CatId,
}

impl CompiledCKY {
    pub fn new() -> Self {
        CompiledCKY {
            binary_rewrites: BinaryRewrites::new(0),
            lexical_rewrites: LexicalRewrites::new(),
            symbols: FxHashMap::default(),
            symbol_names: Vec::new(),
            words: FxHashMap::default(),
            goal_cat: 0,
        }
    }

    /// Intern a category symbol
    pub fn intern_cat(&mut self, name: &str) -> CatId {
        if let Some(&id) = self.symbols.get(name) {
            return id;
        }
        let id = self.symbol_names.len() as CatId;
        self.symbols.insert(name.to_string(), id);
        self.symbol_names.push(name.to_string());
        id
    }

    /// Intern a word
    pub fn intern_word(&mut self, word: &str) -> u32 {
        let next_id = self.words.len() as u32;
        *self.words.entry(word.to_string()).or_insert(next_id)
    }

    /// Finalize grammar after adding all categories
    pub fn finalize(&mut self) {
        let num_cats = self.symbol_names.len();
        self.binary_rewrites = BinaryRewrites::new(num_cats);
    }

    /// Add a binary rule: parent -> left right
    pub fn add_binary_rule(&mut self, parent: &str, left: &str, right: &str) {
        let p = self.intern_cat(parent);
        let l = self.intern_cat(left);
        let r = self.intern_cat(right);
        self.binary_rewrites.add(p, l, r);
    }

    /// Add a lexical rule: cat -> word
    pub fn add_lexical_rule(&mut self, cat: &str, word: &str, prob: f64) {
        let c = self.intern_cat(cat);
        let w = self.intern_word(word);
        self.lexical_rewrites.add(w, c, prob);
    }

    /// Set goal category
    pub fn set_goal(&mut self, goal: &str) {
        self.goal_cat = self.intern_cat(goal);
    }

    /// Parse a sentence - the core compiled algorithm
    ///
    /// This is what a code generator would produce:
    /// - No generic Term representation
    /// - No unification
    /// - No substitution tables
    /// - Direct array indexing
    /// - Inlined semiring operations
    pub fn parse(&self, sentence: &[&str]) -> Option<f64> {
        let n = sentence.len();
        let mut chart = CompiledChart::new(n);

        // Phase 1: Initialize with lexical items
        for (i, word) in sentence.iter().enumerate() {
            if let Some(&word_id) = self.words.get(*word) {
                for &(cat, prob) in self.lexical_rewrites.lookup(word_id) {
                    let phrase = Phrase::new(cat, i as Pos, (i + 1) as Pos);
                    chart.insert(phrase, prob);
                }
            }
        }

        // Phase 2: Bottom-up CKY - process by increasing span length
        // This ensures all sub-constituents exist before we try to combine them.
        for span in 2..=n {
            for i in 0..=n - span {
                let j = i + span;
                // Try all split points k
                for k in (i + 1)..j {
                    // Get all phrases (i,k) and (k,j), combine them
                    let left_phrases: Vec<(Phrase, f64)> = chart
                        .spanning(i as Pos, k as Pos)
                        .iter()
                        .map(|&p| (p, chart.get(&p).unwrap()))
                        .collect();

                    let right_phrases: Vec<(Phrase, f64)> = chart
                        .spanning(k as Pos, j as Pos)
                        .iter()
                        .map(|&p| (p, chart.get(&p).unwrap()))
                        .collect();

                    for (left, left_val) in &left_phrases {
                        for (right, right_val) in &right_phrases {
                            for &parent_cat in self.binary_rewrites.lookup(left.cat, right.cat) {
                                let phrase = Phrase::new(parent_cat, i as Pos, j as Pos);
                                let value = left_val * right_val;
                                chart.insert(phrase, value);
                            }
                        }
                    }
                }
            }
        }

        // Return goal value
        let goal = Phrase::new(self.goal_cat, 0, n as Pos);
        chart.get(&goal)
    }

    /// Parse and return full chart (for debugging)
    pub fn parse_full(&self, sentence: &[&str]) -> CompiledChart {
        let n = sentence.len();
        let mut chart = CompiledChart::new(n);

        // Phase 1: Initialize with lexical items
        for (i, word) in sentence.iter().enumerate() {
            if let Some(&word_id) = self.words.get(*word) {
                for &(cat, prob) in self.lexical_rewrites.lookup(word_id) {
                    let phrase = Phrase::new(cat, i as Pos, (i + 1) as Pos);
                    chart.insert(phrase, prob);
                }
            }
        }

        // Phase 2: Bottom-up CKY - process by increasing span length
        for span in 2..=n {
            for i in 0..=n - span {
                let j = i + span;
                for k in (i + 1)..j {
                    let left_phrases: Vec<(Phrase, f64)> = chart
                        .spanning(i as Pos, k as Pos)
                        .iter()
                        .map(|&p| (p, chart.get(&p).unwrap()))
                        .collect();

                    let right_phrases: Vec<(Phrase, f64)> = chart
                        .spanning(k as Pos, j as Pos)
                        .iter()
                        .map(|&p| (p, chart.get(&p).unwrap()))
                        .collect();

                    for (left, left_val) in &left_phrases {
                        for (right, right_val) in &right_phrases {
                            for &parent_cat in self.binary_rewrites.lookup(left.cat, right.cat) {
                                let phrase = Phrase::new(parent_cat, i as Pos, j as Pos);
                                let value = left_val * right_val;
                                chart.insert(phrase, value);
                            }
                        }
                    }
                }
            }
        }

        chart
    }
}

impl Default for CompiledCKY {
    fn default() -> Self {
        Self::new()
    }
}

/// Create a CKY parser from a grammar specification
pub fn create_parser(
    grammar: &[(&str, &str, &str)],  // (parent, left, right)
    lexicon: &[(&str, &str)],        // (cat, word)
    goal: &str,
) -> CompiledCKY {
    let mut parser = CompiledCKY::new();

    // First pass: collect all categories
    for &(parent, left, right) in grammar {
        parser.intern_cat(parent);
        parser.intern_cat(left);
        parser.intern_cat(right);
    }
    for &(cat, _word) in lexicon {
        parser.intern_cat(cat);
    }
    parser.intern_cat(goal);

    // Finalize to allocate rewrite tables
    parser.finalize();

    // Second pass: add rules
    for &(parent, left, right) in grammar {
        parser.add_binary_rule(parent, left, right);
    }
    for &(cat, word) in lexicon {
        parser.add_lexical_rule(cat, word, 1.0);
    }

    parser.set_goal(goal);
    parser
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_parse() {
        // Grammar: S -> NP VP, NP -> Det N, VP -> V NP
        let grammar = vec![
            ("S", "NP", "VP"),
            ("NP", "Det", "N"),
            ("VP", "V", "NP"),
        ];

        let lexicon = vec![
            ("Det", "the"),
            ("Det", "a"),
            ("N", "dog"),
            ("N", "cat"),
            ("V", "saw"),
            ("V", "chased"),
        ];

        let parser = create_parser(&grammar, &lexicon, "S");

        // "the dog saw the cat"
        let result = parser.parse(&["the", "dog", "saw", "the", "cat"]);
        assert!(result.is_some());
        assert!((result.unwrap() - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_ambiguous_parse() {
        // Grammar with PP attachment ambiguity
        let grammar = vec![
            ("S", "NP", "VP"),
            ("NP", "Det", "N"),
            ("NP", "NP", "PP"),
            ("VP", "V", "NP"),
            ("VP", "VP", "PP"),
            ("PP", "P", "NP"),
        ];

        let lexicon = vec![
            ("Det", "the"),
            ("N", "man"),
            ("N", "telescope"),
            ("V", "saw"),
            ("P", "with"),
        ];

        let parser = create_parser(&grammar, &lexicon, "S");

        // "the man saw the man with the telescope"
        // This has 2 parses (PP attaches to NP or VP)
        let result = parser.parse(&["the", "man", "saw", "the", "man", "with", "the", "telescope"]);
        assert!(result.is_some());
        assert!((result.unwrap() - 2.0).abs() < 1e-10); // 2 parses
    }

    #[test]
    fn test_chart_size() {
        let grammar = vec![
            ("S", "NP", "VP"),
            ("NP", "Det", "N"),
            ("VP", "V", "NP"),
        ];

        let lexicon = vec![
            ("Det", "the"),
            ("N", "dog"),
            ("N", "cat"),
            ("V", "saw"),
        ];

        let parser = create_parser(&grammar, &lexicon, "S");
        let chart = parser.parse_full(&["the", "dog", "saw", "the", "cat"]);

        // Should have phrases for each recognized constituent
        assert!(chart.len() > 0);
        println!("Chart size: {}", chart.len());
    }
}
