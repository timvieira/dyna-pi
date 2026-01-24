//! Code Generator for Specialized Dyna Solvers
//!
//! This module generates specialized Rust source code from a Dyna program.
//! The generated code uses:
//! - Compact struct representations (no generic Terms)
//! - Array-based indexes for bounded domains
//! - Direct field access (no unification)
//! - Inlined semiring operations
//!
//! # Example
//!
//! Input Dyna program:
//! ```text
//! path(I, J) += edge(I, J).
//! path(I, K) += path(I, J) * edge(J, K).
//! ```
//!
//! Generated Rust code:
//! ```rust,ignore
//! #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
//! struct Edge { src: u32, dst: u32 }
//!
//! #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
//! struct Path { src: u32, dst: u32 }
//!
//! struct Solver {
//!     edge_by_src: Vec<Vec<(Edge, f64)>>,
//!     path_values: HashMap<Path, f64>,
//!     path_by_src: Vec<Vec<(Path, f64)>>,
//!     path_by_dst: Vec<Vec<(Path, f64)>>,
//! }
//! ```

use crate::codegen::analysis::{ArgType, FunctorSig, Mode, ProgramAnalysis};
use crate::rule::{Program, Rule};
use crate::term::{Product, Term, Value, VarId};
use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt::Write;
use std::rc::Rc;

/// Configuration for code generation
#[derive(Clone, Debug)]
pub struct CodeGenConfig {
    /// Name for the generated solver struct
    pub solver_name: String,
    /// Semiring type to use (e.g., "f64", "bool", "i64")
    pub value_type: String,
    /// Semiring zero value
    pub zero: String,
    /// Semiring one value
    pub one: String,
    /// Semiring addition operation
    pub plus: String,
    /// Semiring multiplication operation
    pub times: String,
    /// Maximum bound for array indexes (None = use HashMap)
    pub max_array_bound: Option<usize>,
    /// Whether to generate debug output
    pub debug: bool,
}

impl Default for CodeGenConfig {
    fn default() -> Self {
        Self {
            solver_name: "CompiledSolver".to_string(),
            value_type: "f64".to_string(),
            zero: "0.0".to_string(),
            one: "1.0".to_string(),
            plus: "+".to_string(),
            times: "*".to_string(),
            max_array_bound: Some(10000),
            debug: false,
        }
    }
}

impl CodeGenConfig {
    /// Create config for counting semiring
    pub fn counting() -> Self {
        Self {
            value_type: "f64".to_string(),
            zero: "0.0".to_string(),
            one: "1.0".to_string(),
            plus: "+".to_string(),
            times: "*".to_string(),
            ..Default::default()
        }
    }

    /// Create config for boolean semiring
    pub fn boolean() -> Self {
        Self {
            value_type: "bool".to_string(),
            zero: "false".to_string(),
            one: "true".to_string(),
            plus: "||".to_string(),
            times: "&&".to_string(),
            ..Default::default()
        }
    }

    /// Create config for tropical (min-plus) semiring
    pub fn tropical() -> Self {
        Self {
            value_type: "f64".to_string(),
            zero: "f64::INFINITY".to_string(),
            one: "0.0".to_string(),
            plus: ".min".to_string(), // a.min(b)
            times: "+".to_string(),
            ..Default::default()
        }
    }
}

/// Represents the Rust type for a functor argument
#[derive(Clone, Debug)]
pub enum RustType {
    /// Fixed-size integer (u8, u16, u32)
    Int { bits: u8, signed: bool },
    /// String/symbol (uses interned ID)
    SymbolId,
    /// List ID (reference to Cons or Nil)
    ListId,
}

impl RustType {
    fn type_name(&self) -> &'static str {
        match self {
            RustType::Int { bits: 8, signed: false } => "u8",
            RustType::Int { bits: 16, signed: false } => "u16",
            RustType::Int { bits: 32, signed: false } => "u32",
            RustType::Int { bits: 64, signed: false } => "u64",
            RustType::Int { bits: 8, signed: true } => "i8",
            RustType::Int { bits: 16, signed: true } => "i16",
            RustType::Int { bits: 32, signed: true } => "i32",
            RustType::Int { bits: 64, signed: true } => "i64",
            RustType::Int { .. } => "i64",
            RustType::SymbolId => "u32",
            RustType::ListId => "ListId",
        }
    }

    /// Determine Rust type from ArgType analysis
    fn from_arg_type(arg_type: &ArgType, config: &CodeGenConfig) -> Self {
        match arg_type {
            ArgType::Int { min, max } => {
                let (lo, hi) = (min.unwrap_or(0), max.unwrap_or(i64::MAX));

                // Check if fits in array bounds
                if let Some(max_bound) = config.max_array_bound {
                    if lo >= 0 && hi < max_bound as i64 {
                        // Use smallest unsigned type that fits
                        if hi <= u8::MAX as i64 {
                            return RustType::Int { bits: 8, signed: false };
                        } else if hi <= u16::MAX as i64 {
                            return RustType::Int { bits: 16, signed: false };
                        } else if hi <= u32::MAX as i64 {
                            return RustType::Int { bits: 32, signed: false };
                        }
                    }
                }

                // Default to i64 for unbounded
                RustType::Int { bits: 64, signed: true }
            }
            ArgType::Symbol { values: _ } => {
                // Use symbol ID (u32)
                RustType::SymbolId
            }
            ArgType::Term { functor, .. } => {
                // Check if it's a list type
                if functor.as_ref() == "$cons" || functor.as_ref() == "$nil" {
                    RustType::ListId
                } else {
                    // Use i64 as generic value type for other compound terms
                    RustType::Int { bits: 64, signed: true }
                }
            }
            ArgType::Any => {
                // Use i64 as generic value type
                RustType::Int { bits: 64, signed: true }
            }
        }
    }
}

/// Generated struct definition
#[derive(Clone, Debug)]
pub struct GeneratedStruct {
    pub name: String,
    pub fields: Vec<(String, RustType)>,
    pub functor: Rc<str>,
    pub arity: usize,
}

impl GeneratedStruct {
    fn generate_code(&self) -> String {
        let mut code = String::new();

        writeln!(code, "#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]").unwrap();
        writeln!(code, "pub struct {} {{", self.name).unwrap();

        for (field_name, field_type) in &self.fields {
            writeln!(code, "    pub {}: {},", field_name, field_type.type_name()).unwrap();
        }

        writeln!(code, "}}").unwrap();
        code
    }
}

/// Generated index for a query mode
#[derive(Clone, Debug)]
pub struct GeneratedIndex {
    pub name: String,
    pub item_struct: String,
    pub key_fields: Vec<String>,
    pub key_types: Vec<RustType>,
    pub use_array: bool,
    pub array_bounds: Vec<usize>,
}

impl GeneratedIndex {
    fn field_type(&self, config: &CodeGenConfig) -> String {
        if self.use_array {
            // Nested arrays: Vec<Vec<...<Vec<(Item, Value)>>...>>
            let mut ty = format!("Vec<({}, {})>", self.item_struct, config.value_type);
            for _ in 0..self.key_fields.len() {
                ty = format!("Vec<{}>", ty);
            }
            ty
        } else {
            format!("FxHashMap<({}), Vec<({}, {})>>",
                self.key_types.iter().map(|t| t.type_name()).collect::<Vec<_>>().join(", "),
                self.item_struct,
                config.value_type
            )
        }
    }
}

/// Code generator
pub struct CodeGenerator {
    pub config: CodeGenConfig,
    pub analysis: ProgramAnalysis,
    pub structs: FxHashMap<(Rc<str>, usize), GeneratedStruct>,
    pub indexes: Vec<GeneratedIndex>,
    pub symbol_table: FxHashMap<Rc<str>, u32>,
}

impl CodeGenerator {
    /// Create a new code generator from program analysis
    pub fn new(analysis: ProgramAnalysis, config: CodeGenConfig) -> Self {
        let mut gen = Self {
            config,
            analysis,
            structs: FxHashMap::default(),
            indexes: Vec::new(),
            symbol_table: FxHashMap::default(),
        };
        gen.generate_structs();
        gen.generate_indexes();
        gen
    }

    /// Generate struct definitions for all functors
    fn generate_structs(&mut self) {
        for ((functor, arity), sig) in &self.analysis.functors {
            let struct_name = self.functor_to_struct_name(functor);

            let fields: Vec<(String, RustType)> = sig.arg_types
                .iter()
                .enumerate()
                .map(|(i, arg_type)| {
                    let field_name = format!("arg{}", i);
                    let rust_type = RustType::from_arg_type(arg_type, &self.config);
                    (field_name, rust_type)
                })
                .collect();

            let gen_struct = GeneratedStruct {
                name: struct_name,
                fields,
                functor: functor.clone(),
                arity: *arity,
            };

            self.structs.insert((functor.clone(), *arity), gen_struct);
        }
    }

    /// Generate indexes for all query modes
    /// Analyzes rules to determine which indexes are actually needed for joins
    fn generate_indexes(&mut self) {
        let mut needed_indexes: FxHashSet<(Rc<str>, usize, Vec<usize>)> = FxHashSet::default();

        // Analyze each rule to find needed indexes
        for ((functor, arity), drivers) in &self.analysis.drivers {
            for &(rule_idx, trigger_idx) in drivers {
                // Get the rule from program (we'll need to pass program here)
                // For now, add indexes based on functor modes
            }
        }

        // Add indexes from analysis modes
        for ((functor, arity), sig) in &self.analysis.functors {
            for mode in &sig.modes {
                if !mode.is_empty() {
                    needed_indexes.insert((functor.clone(), *arity, mode.clone()));
                }
            }

            // Also add single-position indexes for each position (needed for various joins)
            for i in 0..*arity {
                needed_indexes.insert((functor.clone(), *arity, vec![i]));
            }
        }

        // Create index definitions
        for (functor, arity, positions) in needed_indexes {
            let struct_name = self.functor_to_struct_name(&functor);
            let sig = match self.analysis.functors.get(&(functor.clone(), arity)) {
                Some(s) => s,
                None => continue,
            };

            let index_name = format!("{}_by_{}",
                functor.to_lowercase(),
                positions.iter().map(|i| format!("arg{}", i)).collect::<Vec<_>>().join("_")
            );

            // Skip if we already have this index
            if self.indexes.iter().any(|idx| idx.name == index_name) {
                continue;
            }

            let key_fields: Vec<String> = positions.iter()
                .map(|&i| format!("arg{}", i))
                .collect();

            let key_types: Vec<RustType> = positions.iter()
                .map(|&i| RustType::from_arg_type(&sig.arg_types[i], &self.config))
                .collect();

            // Check if we can use array indexing
            let (use_array, bounds) = self.check_array_bounds(&sig.arg_types, &positions);

            self.indexes.push(GeneratedIndex {
                name: index_name,
                item_struct: struct_name.clone(),
                key_fields,
                key_types,
                use_array,
                array_bounds: bounds,
            });
        }
    }

    /// Check if mode can use array indexing
    fn check_array_bounds(&self, arg_types: &[ArgType], mode: &Mode) -> (bool, Vec<usize>) {
        let max_bound = self.config.max_array_bound.unwrap_or(0);
        if max_bound == 0 {
            return (false, vec![]);
        }

        let mut bounds = Vec::new();
        for &i in mode {
            match &arg_types[i] {
                ArgType::Int { min: Some(lo), max: Some(hi) } if *lo >= 0 => {
                    let range = (*hi - *lo + 1) as usize;
                    if range <= max_bound {
                        bounds.push(range);
                    } else {
                        return (false, vec![]);
                    }
                }
                _ => return (false, vec![]),
            }
        }
        (true, bounds)
    }

    /// Convert functor name to struct name (PascalCase)
    fn functor_to_struct_name(&self, functor: &str) -> String {
        let mut result = String::new();
        let mut capitalize_next = true;

        for c in functor.chars() {
            if c == '_' || c == '-' {
                capitalize_next = true;
            } else if capitalize_next {
                result.push(c.to_ascii_uppercase());
                capitalize_next = false;
            } else {
                result.push(c);
            }
        }
        result
    }

    /// Generate the complete Rust source code
    pub fn generate(&self, program: &Program) -> String {
        let mut code = String::new();

        // Header
        writeln!(code, "//! Auto-generated specialized solver").unwrap();
        writeln!(code, "//! DO NOT EDIT - generated by Dyna code generator").unwrap();
        writeln!(code).unwrap();
        writeln!(code, "#![allow(unused_variables, dead_code)]").unwrap();
        writeln!(code).unwrap();

        // Imports
        writeln!(code, "use rustc_hash::{{FxHashMap, FxHashSet}};").unwrap();
        writeln!(code, "use std::collections::VecDeque;").unwrap();
        writeln!(code).unwrap();

        // Check if lists are used
        let uses_lists = self.structs.values().any(|s| {
            s.functor.as_ref() == "$cons" || s.functor.as_ref() == "$nil" ||
            s.fields.iter().any(|(_, t)| matches!(t, RustType::ListId))
        });

        if uses_lists {
            // List infrastructure
            writeln!(code, "// ============ List Support ============").unwrap();
            writeln!(code, "/// List ID - 0 is Nil, positive values index into cons_cells").unwrap();
            writeln!(code, "pub type ListId = usize;").unwrap();
            writeln!(code, "pub const NIL: ListId = 0;").unwrap();
            writeln!(code).unwrap();
            writeln!(code, "/// A cons cell: (head, tail)").unwrap();
            writeln!(code, "#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]").unwrap();
            writeln!(code, "pub struct ConsCell {{").unwrap();
            writeln!(code, "    pub head: i64,").unwrap();
            writeln!(code, "    pub tail: ListId,").unwrap();
            writeln!(code, "}}").unwrap();
            writeln!(code).unwrap();
        }

        // Struct definitions
        writeln!(code, "// ============ Item Structs ============").unwrap();
        for gen_struct in self.structs.values() {
            writeln!(code, "{}", gen_struct.generate_code()).unwrap();
        }

        // Solver struct
        writeln!(code, "// ============ Solver ============").unwrap();
        code.push_str(&self.generate_solver_struct());

        // Solver impl
        code.push_str(&self.generate_solver_impl(program));

        code
    }

    /// Generate the solver struct definition
    fn generate_solver_struct(&self) -> String {
        let mut code = String::new();

        writeln!(code, "pub struct {} {{", self.config.solver_name).unwrap();

        // Value maps for each functor
        for gen_struct in self.structs.values() {
            writeln!(code, "    {}_values: FxHashMap<{}, {}>,",
                gen_struct.functor.to_lowercase(),
                gen_struct.name,
                self.config.value_type
            ).unwrap();
        }

        // Indexes
        for index in &self.indexes {
            writeln!(code, "    {}: {},",
                index.name,
                index.field_type(&self.config)
            ).unwrap();
        }

        // Agenda
        writeln!(code, "    agenda: VecDeque<AgendaItem>,").unwrap();

        // List support (if needed)
        let uses_lists = self.structs.values().any(|s| {
            s.functor.as_ref() == "$cons" || s.functor.as_ref() == "$nil" ||
            s.fields.iter().any(|(_, t)| matches!(t, RustType::ListId))
        });
        if uses_lists {
            writeln!(code, "    /// Cons cells table (index 0 is unused, NIL=0)").unwrap();
            writeln!(code, "    cons_cells: Vec<ConsCell>,").unwrap();
            writeln!(code, "    /// Map from cons cell content to ID for deduplication").unwrap();
            writeln!(code, "    cons_lookup: FxHashMap<ConsCell, ListId>,").unwrap();
        }

        writeln!(code, "}}").unwrap();
        writeln!(code).unwrap();

        // Agenda item enum
        writeln!(code, "#[derive(Clone, Debug)]").unwrap();
        writeln!(code, "enum AgendaItem {{").unwrap();
        for gen_struct in self.structs.values() {
            writeln!(code, "    {}({}, {}),",
                gen_struct.name,
                gen_struct.name,
                self.config.value_type
            ).unwrap();
        }
        writeln!(code, "}}").unwrap();

        code
    }

    /// Generate the solver implementation
    fn generate_solver_impl(&self, program: &Program) -> String {
        let mut code = String::new();

        writeln!(code, "\nimpl {} {{", self.config.solver_name).unwrap();

        // Constructor
        code.push_str(&self.generate_constructor());

        // List methods (if needed)
        code.push_str(&self.generate_list_methods());

        // Update methods
        code.push_str(&self.generate_update_methods());

        // Solve method
        code.push_str(&self.generate_solve_method(program));

        // Query methods
        code.push_str(&self.generate_query_methods());

        writeln!(code, "}}").unwrap();

        code
    }

    /// Generate constructor
    fn generate_constructor(&self) -> String {
        let mut code = String::new();

        writeln!(code, "    pub fn new() -> Self {{").unwrap();
        writeln!(code, "        Self {{").unwrap();

        for gen_struct in self.structs.values() {
            writeln!(code, "            {}_values: FxHashMap::default(),",
                gen_struct.functor.to_lowercase()
            ).unwrap();
        }

        for index in &self.indexes {
            if index.use_array {
                // Initialize nested arrays
                let mut init = "Vec::new()".to_string();
                for &bound in index.array_bounds.iter().rev() {
                    init = format!("vec![{}; {}]", init, bound);
                }
                writeln!(code, "            {}: {},", index.name, init).unwrap();
            } else {
                writeln!(code, "            {}: FxHashMap::default(),", index.name).unwrap();
            }
        }

        writeln!(code, "            agenda: VecDeque::new(),").unwrap();

        // List support initialization
        let uses_lists = self.structs.values().any(|s| {
            s.functor.as_ref() == "$cons" || s.functor.as_ref() == "$nil" ||
            s.fields.iter().any(|(_, t)| matches!(t, RustType::ListId))
        });
        if uses_lists {
            writeln!(code, "            cons_cells: vec![ConsCell {{ head: 0, tail: 0 }}], // index 0 unused").unwrap();
            writeln!(code, "            cons_lookup: FxHashMap::default(),").unwrap();
        }

        writeln!(code, "        }}").unwrap();
        writeln!(code, "    }}").unwrap();

        code
    }

    /// Generate list helper methods
    fn generate_list_methods(&self) -> String {
        let mut code = String::new();

        let uses_lists = self.structs.values().any(|s| {
            s.functor.as_ref() == "$cons" || s.functor.as_ref() == "$nil" ||
            s.fields.iter().any(|(_, t)| matches!(t, RustType::ListId))
        });

        if uses_lists {
            writeln!(code, "\n    // ============ List Methods ============").unwrap();

            // cons method - create or look up a cons cell
            writeln!(code, "    /// Create or look up a cons cell").unwrap();
            writeln!(code, "    pub fn cons(&mut self, head: i64, tail: ListId) -> ListId {{").unwrap();
            writeln!(code, "        let cell = ConsCell {{ head, tail }};").unwrap();
            writeln!(code, "        if let Some(&id) = self.cons_lookup.get(&cell) {{").unwrap();
            writeln!(code, "            id").unwrap();
            writeln!(code, "        }} else {{").unwrap();
            writeln!(code, "            let id = self.cons_cells.len();").unwrap();
            writeln!(code, "            self.cons_cells.push(cell);").unwrap();
            writeln!(code, "            self.cons_lookup.insert(cell, id);").unwrap();
            writeln!(code, "            id").unwrap();
            writeln!(code, "        }}").unwrap();
            writeln!(code, "    }}").unwrap();

            // is_nil method
            writeln!(code, "\n    /// Check if a list ID is nil").unwrap();
            writeln!(code, "    #[inline]").unwrap();
            writeln!(code, "    pub fn is_nil(&self, id: ListId) -> bool {{").unwrap();
            writeln!(code, "        id == NIL").unwrap();
            writeln!(code, "    }}").unwrap();

            // is_cons method
            writeln!(code, "\n    /// Check if a list ID is a cons cell").unwrap();
            writeln!(code, "    #[inline]").unwrap();
            writeln!(code, "    pub fn is_cons(&self, id: ListId) -> bool {{").unwrap();
            writeln!(code, "        id != NIL && id < self.cons_cells.len()").unwrap();
            writeln!(code, "    }}").unwrap();

            // get_cons method
            writeln!(code, "\n    /// Get the head and tail of a cons cell").unwrap();
            writeln!(code, "    pub fn get_cons(&self, id: ListId) -> Option<(i64, ListId)> {{").unwrap();
            writeln!(code, "        if id != NIL && id < self.cons_cells.len() {{").unwrap();
            writeln!(code, "            let cell = &self.cons_cells[id];").unwrap();
            writeln!(code, "            Some((cell.head, cell.tail))").unwrap();
            writeln!(code, "        }} else {{").unwrap();
            writeln!(code, "            None").unwrap();
            writeln!(code, "        }}").unwrap();
            writeln!(code, "    }}").unwrap();
        }

        code
    }

    /// Generate update methods for each functor
    fn generate_update_methods(&self) -> String {
        let mut code = String::new();

        for gen_struct in self.structs.values() {
            let fn_name = gen_struct.functor.to_lowercase();
            let struct_name = &gen_struct.name;
            let value_type = &self.config.value_type;

            writeln!(code, "\n    /// Update {} item with delta value", fn_name).unwrap();
            writeln!(code, "    pub fn update_{}(&mut self, item: {}, delta: {}) {{",
                fn_name, struct_name, value_type
            ).unwrap();

            writeln!(code, "        let entry = self.{}_values.entry(item).or_insert({});",
                fn_name, self.config.zero
            ).unwrap();

            // Apply semiring plus
            if self.config.plus == "+" {
                writeln!(code, "        let old = *entry;").unwrap();
                writeln!(code, "        *entry = *entry + delta;").unwrap();
            } else if self.config.plus == "||" {
                writeln!(code, "        let old = *entry;").unwrap();
                writeln!(code, "        *entry = *entry || delta;").unwrap();
            } else if self.config.plus == ".min" {
                writeln!(code, "        let old = *entry;").unwrap();
                writeln!(code, "        *entry = (*entry).min(delta);").unwrap();
            } else {
                writeln!(code, "        let old = *entry;").unwrap();
                writeln!(code, "        *entry = *entry {} delta;", self.config.plus).unwrap();
            }

            // Check if value changed
            writeln!(code, "        if old != *entry {{").unwrap();
            writeln!(code, "            self.agenda.push_back(AgendaItem::{}(item, delta));",
                struct_name
            ).unwrap();

            // Update indexes
            for index in &self.indexes {
                if index.item_struct == *struct_name {
                    code.push_str(&self.generate_index_update(index, "item", "delta"));
                }
            }

            writeln!(code, "        }}").unwrap();
            writeln!(code, "    }}").unwrap();
        }

        code
    }

    /// Generate index update code
    fn generate_index_update(&self, index: &GeneratedIndex, item_var: &str, value_var: &str) -> String {
        let mut code = String::new();

        if index.use_array {
            // Array-based index
            let mut access = format!("self.{}", index.name);
            for field in &index.key_fields {
                access = format!("{}[{}.{} as usize]", access, item_var, field);
            }
            writeln!(code, "            {}.push(({}, {}));",
                access, item_var, value_var
            ).unwrap();
        } else {
            // HashMap-based index
            let key = if index.key_fields.len() == 1 {
                format!("{}.{}", item_var, index.key_fields[0])
            } else {
                format!("({})", index.key_fields.iter()
                    .map(|f| format!("{}.{}", item_var, f))
                    .collect::<Vec<_>>()
                    .join(", "))
            };
            writeln!(code, "            self.{}.entry({}).or_default().push(({}, {}));",
                index.name, key, item_var, value_var
            ).unwrap();
        }

        code
    }

    /// Generate the main solve method
    fn generate_solve_method(&self, program: &Program) -> String {
        let mut code = String::new();

        writeln!(code, "\n    /// Run forward chaining to fixpoint").unwrap();
        writeln!(code, "    pub fn solve(&mut self) {{").unwrap();
        writeln!(code, "        while let Some(trigger) = self.agenda.pop_front() {{").unwrap();
        writeln!(code, "            match trigger {{").unwrap();

        // Generate match arms for each item type
        for gen_struct in self.structs.values() {
            writeln!(code, "                AgendaItem::{}(item, delta) => {{",
                gen_struct.name
            ).unwrap();

            // Find rules driven by this functor
            let key = (gen_struct.functor.clone(), gen_struct.arity);
            if let Some(drivers) = self.analysis.drivers.get(&key) {
                for &(rule_idx, subgoal_idx) in drivers {
                    if let Some(rule) = program.iter().nth(rule_idx) {
                        code.push_str(&self.generate_rule_firing(
                            rule, rule_idx, subgoal_idx, gen_struct
                        ));
                    }
                }
            }

            writeln!(code, "                }}").unwrap();
        }

        writeln!(code, "            }}").unwrap();
        writeln!(code, "        }}").unwrap();
        writeln!(code, "    }}").unwrap();

        code
    }

    /// Generate code for firing a specific rule
    fn generate_rule_firing(
        &self,
        rule: &Rule,
        rule_idx: usize,
        trigger_idx: usize,
        _trigger_struct: &GeneratedStruct
    ) -> String {
        let mut code = String::new();
        let base_indent = "                    ";

        writeln!(code, "{}// Rule {}: {} :- ...", base_indent, rule_idx, rule.head).unwrap();

        // Collect variable bindings from trigger
        let trigger_subgoal = &rule.body[trigger_idx];
        let mut bindings: FxHashMap<VarId, String> = FxHashMap::default();

        if let Term::Compound { args, .. } = trigger_subgoal {
            for (i, arg) in args.iter().enumerate() {
                if let Term::Var(v) = arg {
                    bindings.insert(*v, format!("item.arg{}", i));
                }
            }
        }

        // Track open braces for proper closing
        let mut open_braces: Vec<&str> = Vec::new();
        let mut current_indent = base_indent.to_string();

        // Generate nested loops for other subgoals
        for (idx, subgoal) in rule.body.iter().enumerate() {
            if idx == trigger_idx {
                continue;
            }

            if let Term::Compound { functor, args } = subgoal {
                // Check for builtin predicates
                if let Some(builtin_code) = self.generate_builtin(functor, args, &bindings, &current_indent, idx) {
                    code.push_str(&builtin_code);
                    open_braces.push("if");
                    current_indent.push_str("    ");

                    // Collect any new bindings from the builtin (for $is and $unify)
                    if functor.as_ref() == "$is" {
                        if let Some(Term::Var(v)) = args.first() {
                            if !bindings.contains_key(v) {
                                // The LHS of 'is' is being bound
                                bindings.insert(*v, format!("_is_result_{}", idx));
                            }
                        }
                    } else if functor.as_ref() == "$unify" && args.len() == 2 {
                        // For unification, bind any unbound variables
                        match (&args[0], &args[1]) {
                            (Term::Var(v1), Term::Var(v2)) => {
                                let b1 = bindings.contains_key(v1);
                                let b2 = bindings.contains_key(v2);
                                if !b1 && b2 {
                                    bindings.insert(*v1, format!("_unify_result_{}", idx));
                                } else if b1 && !b2 {
                                    bindings.insert(*v2, format!("_unify_result_{}", idx));
                                }
                                // If both unbound, we could bind both but skip for simplicity
                            }
                            (Term::Var(v), _) => {
                                if !bindings.contains_key(v) {
                                    bindings.insert(*v, format!("_unify_result_{}", idx));
                                }
                            }
                            (_, Term::Var(v)) => {
                                if !bindings.contains_key(v) {
                                    bindings.insert(*v, format!("_unify_result_{}", idx));
                                }
                            }
                            _ => {}
                        }
                    }
                    continue;
                }

                let sg_struct = self.structs.get(&(functor.clone(), args.len()));
                if let Some(sg_struct) = sg_struct {
                    // Find bound positions (where we have a binding for that variable)
                    let bound_positions: Vec<usize> = args.iter()
                        .enumerate()
                        .filter_map(|(i, arg)| {
                            if let Term::Var(v) = arg {
                                if bindings.contains_key(v) { Some(i) } else { None }
                            } else {
                                Some(i) // Constants are always bound
                            }
                        })
                        .collect();

                    let iter_var = format!("sg{}", idx);
                    let val_var = format!("val{}", idx);

                    if bound_positions.is_empty() {
                        // Iterate over all items
                        writeln!(code, "{}for (&{}, &{}) in &self.{}_values {{",
                            current_indent, iter_var, val_var, functor.to_lowercase()
                        ).unwrap();
                        open_braces.push("for");
                        current_indent.push_str("    ");
                    } else {
                        // Find matching index - must match EXACT positions, not just count
                        let expected_key_fields: Vec<String> = bound_positions.iter()
                            .map(|&i| format!("arg{}", i))
                            .collect();

                        let index = self.indexes.iter().find(|idx|
                            idx.item_struct == sg_struct.name &&
                            idx.key_fields == expected_key_fields
                        );

                        if let Some(index) = index {
                            // Build key expressions matching the index's key_fields order
                            let key_exprs: Vec<String> = bound_positions.iter()
                                .map(|&i| {
                                    if let Term::Var(v) = &args[i] {
                                        bindings.get(v).cloned()
                                            .unwrap_or_else(|| format!("/* unbound {} */", v))
                                    } else if let Term::Const(c) = &args[i] {
                                        match c {
                                            Value::Int(n) => format!("{}", n),
                                            Value::Symbol(s) => format!("/* symbol {} */", s),
                                            _ => format!("/* const */"),
                                        }
                                    } else {
                                        format!("/* complex at {} */", i)
                                    }
                                })
                                .collect();

                            if index.use_array {
                                let mut access = format!("self.{}", index.name);
                                for key in &key_exprs {
                                    access = format!("{}[{} as usize]", access, key);
                                }
                                writeln!(code, "{}for &({}, {}) in &{} {{",
                                    current_indent, iter_var, val_var, access
                                ).unwrap();
                                open_braces.push("for");
                                current_indent.push_str("    ");
                            } else {
                                // HashMap lookup with if-let
                                let key = if key_exprs.len() == 1 {
                                    format!("{}", key_exprs[0])
                                } else {
                                    format!("({})", key_exprs.join(", "))
                                };
                                writeln!(code, "{}if let Some(items) = self.{}.get(&{}) {{",
                                    current_indent, index.name, key
                                ).unwrap();
                                open_braces.push("if-let");
                                current_indent.push_str("    ");

                                writeln!(code, "{}for &({}, {}) in items {{",
                                    current_indent, iter_var, val_var
                                ).unwrap();
                                open_braces.push("for");
                                current_indent.push_str("    ");
                            }
                        } else {
                            // Fallback: iterate over all with filter
                            writeln!(code, "{}for (&{}, &{}) in &self.{}_values {{",
                                current_indent, iter_var, val_var, functor.to_lowercase()
                            ).unwrap();
                            open_braces.push("for");
                            current_indent.push_str("    ");

                            // Add constraint checks for bound variables
                            let mut constraints = Vec::new();
                            for &i in &bound_positions {
                                if let Term::Var(v) = &args[i] {
                                    if let Some(binding) = bindings.get(v) {
                                        constraints.push(format!("{}.arg{} == {} as i64", iter_var, i, binding));
                                    }
                                }
                            }
                            if !constraints.is_empty() {
                                writeln!(code, "{}if {} {{",
                                    current_indent, constraints.join(" && ")
                                ).unwrap();
                                open_braces.push("if");
                                current_indent.push_str("    ");
                            }
                        }
                    }

                    // Add constraint checks for variables that appear multiple times in this subgoal
                    // AND for join constraints with previously bound variables
                    let mut join_constraints = Vec::new();
                    for (i, arg) in args.iter().enumerate() {
                        if let Term::Var(v) = arg {
                            if let Some(existing) = bindings.get(v) {
                                // This variable was already bound - add constraint check
                                // But only if we're in a full scan (no index used)
                                if bound_positions.contains(&i) {
                                    // Already handled by index lookup
                                } else {
                                    // Variable appears but wasn't used in index - need constraint
                                    join_constraints.push(format!("{}.arg{} == {} as i64", iter_var, i, existing));
                                }
                            }
                        }
                    }
                    if !join_constraints.is_empty() {
                        writeln!(code, "{}if {} {{",
                            current_indent, join_constraints.join(" && ")
                        ).unwrap();
                        open_braces.push("if");
                        current_indent.push_str("    ");
                    }

                    // Collect new bindings from this subgoal
                    for (i, arg) in args.iter().enumerate() {
                        if let Term::Var(v) = arg {
                            if !bindings.contains_key(v) {
                                bindings.insert(*v, format!("{}.arg{}", iter_var, i));
                            }
                        }
                    }
                }
            }
        }

        // Generate head construction and update
        if let Term::Compound { functor, args } = &rule.head {
            if let Some(head_struct) = self.structs.get(&(functor.clone(), args.len())) {
                // Compute value expression (skip builtins - they don't contribute values)
                let mut value_terms = vec!["delta".to_string()];
                for (idx, subgoal) in rule.body.iter().enumerate() {
                    if idx != trigger_idx {
                        // Skip builtins - they're constraints, not value contributors
                        // ($cons and $nil are data constructors, not builtins)
                        if let Term::Compound { functor: sg_functor, .. } = subgoal {
                            if sg_functor.starts_with('$') && sg_functor.as_ref() != "$cons" && sg_functor.as_ref() != "$nil" {
                                continue;
                            }
                        }
                        value_terms.push(format!("val{}", idx));
                    }
                }

                let value_expr = if self.config.times == "*" {
                    value_terms.join(" * ")
                } else {
                    value_terms.join(&format!(" {} ", self.config.times))
                };

                writeln!(code, "{}let value = {};", current_indent, value_expr).unwrap();

                // Construct head item
                let head_args: Vec<String> = args.iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        self.term_to_head_arg(arg, &bindings, &head_struct.fields[i].1)
                    })
                    .collect();

                let field_inits: Vec<String> = head_struct.fields.iter()
                    .zip(&head_args)
                    .map(|((name, _), val)| format!("{}: {}", name, val))
                    .collect();

                writeln!(code, "{}let head = {} {{ {} }};",
                    current_indent, head_struct.name, field_inits.join(", ")
                ).unwrap();

                writeln!(code, "{}self.update_{}(head, value);",
                    current_indent, functor.to_lowercase()
                ).unwrap();
            }
        }

        // Close all open braces in reverse order
        while let Some(_brace_type) = open_braces.pop() {
            current_indent.truncate(current_indent.len().saturating_sub(4));
            writeln!(code, "{}}}", current_indent).unwrap();
        }

        code
    }

    /// Generate code for builtin predicates.
    /// Returns Some(code) if this is a builtin, None otherwise.
    fn generate_builtin(
        &self,
        functor: &str,
        args: &[Term],
        bindings: &FxHashMap<VarId, String>,
        indent: &str,
        subgoal_idx: usize,
    ) -> Option<String> {
        let mut code = String::new();

        match functor {
            // Comparison builtins
            "$lt" | "$le" | "$gt" | "$ge" | "$eq" | "$ne" => {
                if args.len() != 2 {
                    return None;
                }

                let op = match functor {
                    "$lt" => "<",
                    "$le" => "<=",
                    "$gt" => ">",
                    "$ge" => ">=",
                    "$eq" => "==",
                    "$ne" => "!=",
                    _ => return None,
                };

                let lhs = self.term_to_expr(&args[0], bindings)?;
                let rhs = self.term_to_expr(&args[1], bindings)?;

                writeln!(code, "{}if {} {} {} {{", indent, lhs, op, rhs).unwrap();
                Some(code)
            }

            // Arithmetic assignment
            "$is" => {
                if args.len() != 2 {
                    return None;
                }

                let lhs = &args[0];
                let rhs_expr = self.arith_to_expr(&args[1], bindings)?;

                match lhs {
                    Term::Var(v) => {
                        if let Some(binding) = bindings.get(v) {
                            // Variable is already bound - this is a check
                            writeln!(code, "{}if {} == ({}) {{", indent, binding, rhs_expr).unwrap();
                        } else {
                            // Variable is being bound - compute and assign
                            writeln!(code, "{}let _is_result_{} = {};", indent, subgoal_idx, rhs_expr).unwrap();
                            writeln!(code, "{}if true {{", indent).unwrap();
                        }
                    }
                    _ => {
                        // LHS is a constant - check equality
                        let lhs_expr = self.term_to_expr(lhs, bindings)?;
                        writeln!(code, "{}if {} == ({}) {{", indent, lhs_expr, rhs_expr).unwrap();
                    }
                }

                Some(code)
            }

            // Unification
            "$unify" => {
                if args.len() != 2 {
                    return None;
                }

                let lhs = &args[0];
                let rhs = &args[1];

                match (lhs, rhs) {
                    // Both are variables
                    (Term::Var(v1), Term::Var(v2)) => {
                        let b1 = bindings.get(v1);
                        let b2 = bindings.get(v2);
                        match (b1, b2) {
                            (Some(e1), Some(e2)) => {
                                // Both bound - check equality
                                writeln!(code, "{}if {} == {} {{", indent, e1, e2).unwrap();
                            }
                            (Some(e1), None) => {
                                // Bind v2 to v1's value
                                writeln!(code, "{}let _unify_result_{} = {};", indent, subgoal_idx, e1).unwrap();
                                writeln!(code, "{}if true {{", indent).unwrap();
                            }
                            (None, Some(e2)) => {
                                // Bind v1 to v2's value
                                writeln!(code, "{}let _unify_result_{} = {};", indent, subgoal_idx, e2).unwrap();
                                writeln!(code, "{}if true {{", indent).unwrap();
                            }
                            (None, None) => {
                                // Both unbound - create shared binding (simplified)
                                writeln!(code, "{}// Both variables unbound - treating as always true", indent).unwrap();
                                writeln!(code, "{}if true {{", indent).unwrap();
                            }
                        }
                    }
                    // LHS is variable, RHS is constant/term
                    (Term::Var(v), _) => {
                        if let Some(binding) = bindings.get(v) {
                            // Variable is bound - check equality
                            if let Some(rhs_expr) = self.term_to_expr(rhs, bindings) {
                                writeln!(code, "{}if {} == {} {{", indent, binding, rhs_expr).unwrap();
                            } else {
                                return None;
                            }
                        } else {
                            // Variable is unbound - bind it
                            if let Some(rhs_expr) = self.term_to_expr(rhs, bindings) {
                                writeln!(code, "{}let _unify_result_{} = {};", indent, subgoal_idx, rhs_expr).unwrap();
                                writeln!(code, "{}if true {{", indent).unwrap();
                            } else {
                                return None;
                            }
                        }
                    }
                    // LHS is constant/term, RHS is variable
                    (_, Term::Var(v)) => {
                        if let Some(binding) = bindings.get(v) {
                            // Variable is bound - check equality
                            if let Some(lhs_expr) = self.term_to_expr(lhs, bindings) {
                                writeln!(code, "{}if {} == {} {{", indent, lhs_expr, binding).unwrap();
                            } else {
                                return None;
                            }
                        } else {
                            // Variable is unbound - bind it
                            if let Some(lhs_expr) = self.term_to_expr(lhs, bindings) {
                                writeln!(code, "{}let _unify_result_{} = {};", indent, subgoal_idx, lhs_expr).unwrap();
                                writeln!(code, "{}if true {{", indent).unwrap();
                            } else {
                                return None;
                            }
                        }
                    }
                    // Both are constants/terms
                    _ => {
                        if let (Some(lhs_expr), Some(rhs_expr)) =
                            (self.term_to_expr(lhs, bindings), self.term_to_expr(rhs, bindings)) {
                            writeln!(code, "{}if {} == {} {{", indent, lhs_expr, rhs_expr).unwrap();
                        } else {
                            return None;
                        }
                    }
                }

                Some(code)
            }

            // $fail - always fails, prevents rule from firing
            "$fail" => {
                // Generate code that will never execute (always false condition)
                writeln!(code, "{}if false {{", indent).unwrap();
                Some(code)
            }

            // Free/bound checks
            "$free" => {
                if args.len() != 1 {
                    return None;
                }
                if let Term::Var(v) = &args[0] {
                    if !bindings.contains_key(v) {
                        // Variable is free - condition succeeds
                        writeln!(code, "{}if true {{", indent).unwrap();
                        Some(code)
                    } else {
                        // Variable is bound - condition fails
                        writeln!(code, "{}if false {{", indent).unwrap();
                        Some(code)
                    }
                } else {
                    // Non-variable argument - always bound
                    writeln!(code, "{}if false {{", indent).unwrap();
                    Some(code)
                }
            }

            "$bound" => {
                if args.len() != 1 {
                    return None;
                }
                if let Term::Var(v) = &args[0] {
                    if bindings.contains_key(v) {
                        // Variable is bound - condition succeeds
                        writeln!(code, "{}if true {{", indent).unwrap();
                        Some(code)
                    } else {
                        // Variable is free - condition fails
                        writeln!(code, "{}if false {{", indent).unwrap();
                        Some(code)
                    }
                } else {
                    // Non-variable argument - always bound
                    writeln!(code, "{}if true {{", indent).unwrap();
                    Some(code)
                }
            }

            // Not-matches check
            "$not_matches" | "$neq" => {
                if args.len() != 2 {
                    return None;
                }

                // For simple cases where both are bound
                if let (Some(lhs), Some(rhs)) = (
                    self.term_to_expr(&args[0], bindings),
                    self.term_to_expr(&args[1], bindings),
                ) {
                    writeln!(code, "{}if {} != {} {{", indent, lhs, rhs).unwrap();
                    Some(code)
                } else {
                    // Can't determine at compile time - skip
                    None
                }
            }

            // Chained comparisons (0 <= X <= Y < 3)
            "$chain" => {
                // Each arg is a comparison term
                let mut conditions = Vec::new();

                for arg in args {
                    if let Term::Compound { functor, args: cmp_args } = arg {
                        if cmp_args.len() == 2 {
                            let op = match functor.as_ref() {
                                "$lt" => "<",
                                "$le" => "<=",
                                "$gt" => ">",
                                "$ge" => ">=",
                                "$eq" => "==",
                                "$ne" => "!=",
                                _ => continue,
                            };

                            if let (Some(lhs), Some(rhs)) = (
                                self.term_to_expr(&cmp_args[0], bindings),
                                self.term_to_expr(&cmp_args[1], bindings),
                            ) {
                                conditions.push(format!("{} {} {}", lhs, op, rhs));
                            }
                        }
                    }
                }

                if !conditions.is_empty() {
                    let combined = conditions.join(" && ");
                    writeln!(code, "{}if {} {{", indent, combined).unwrap();
                    Some(code)
                } else {
                    None
                }
            }

            _ => None,
        }
    }

    /// Convert a term to a head argument expression.
    /// Handles variables, constants, and compound terms like $cons(X, Xs).
    fn term_to_head_arg(&self, term: &Term, bindings: &FxHashMap<VarId, String>, rust_type: &RustType) -> String {
        match term {
            Term::Var(v) => {
                bindings.get(v)
                    .map(|s| format!("{} as {}", s, rust_type.type_name()))
                    .unwrap_or_else(|| format!("/* unbound {} */", v))
            }
            Term::Const(c) => {
                match c {
                    Value::Int(n) => format!("{} as {}", n, rust_type.type_name()),
                    Value::Symbol(s) => format!("/* symbol {} */", s),
                    Value::Float(f) => format!("{} as {}", f.into_inner(), rust_type.type_name()),
                    Value::Bool(b) => format!("{}", b),
                    _ => "/* const */".to_string(),
                }
            }
            Term::Compound { functor, args } => {
                // Handle list constructors
                if functor.as_ref() == "$nil" {
                    "NIL".to_string()
                } else if functor.as_ref() == "$cons" && args.len() == 2 {
                    // Cons cell: construct using self.cons(head, tail)
                    let head_expr = self.term_to_head_arg(&args[0], bindings, &RustType::Int { bits: 64, signed: true });
                    let tail_expr = self.term_to_head_arg(&args[1], bindings, &RustType::ListId);
                    format!("self.cons({}, {})", head_expr, tail_expr)
                } else {
                    format!("/* complex: {}(...) */", functor)
                }
            }
            _ => "/* unknown */".to_string(),
        }
    }

    /// Convert a term to a Rust expression string.
    fn term_to_expr(&self, term: &Term, bindings: &FxHashMap<VarId, String>) -> Option<String> {
        match term {
            Term::Var(v) => bindings.get(v).cloned(),
            Term::Const(Value::Int(n)) => Some(format!("{}", n)),
            Term::Const(Value::Float(f)) => Some(format!("{}", f.into_inner())),
            Term::Const(Value::Bool(b)) => Some(format!("{}", b)),
            _ => None,
        }
    }

    /// Convert an arithmetic term to a Rust expression string.
    fn arith_to_expr(&self, term: &Term, bindings: &FxHashMap<VarId, String>) -> Option<String> {
        match term {
            Term::Var(v) => bindings.get(v).map(|s| format!("({} as f64)", s)),
            Term::Const(Value::Int(n)) => Some(format!("{}.0", n)),
            Term::Const(Value::Float(f)) => Some(format!("{}", f.into_inner())),

            Term::Compound { functor, args } => {
                match functor.as_ref() {
                    "$add" if args.len() == 2 => {
                        let l = self.arith_to_expr(&args[0], bindings)?;
                        let r = self.arith_to_expr(&args[1], bindings)?;
                        Some(format!("({} + {})", l, r))
                    }
                    "$sub" if args.len() == 2 => {
                        let l = self.arith_to_expr(&args[0], bindings)?;
                        let r = self.arith_to_expr(&args[1], bindings)?;
                        Some(format!("({} - {})", l, r))
                    }
                    "$mul" if args.len() == 2 => {
                        let l = self.arith_to_expr(&args[0], bindings)?;
                        let r = self.arith_to_expr(&args[1], bindings)?;
                        Some(format!("({} * {})", l, r))
                    }
                    "$div" if args.len() == 2 => {
                        let l = self.arith_to_expr(&args[0], bindings)?;
                        let r = self.arith_to_expr(&args[1], bindings)?;
                        Some(format!("({} / {})", l, r))
                    }
                    "$neg" if args.len() == 1 => {
                        let a = self.arith_to_expr(&args[0], bindings)?;
                        Some(format!("(-{})", a))
                    }
                    "$abs" if args.len() == 1 => {
                        let a = self.arith_to_expr(&args[0], bindings)?;
                        Some(format!("({}).abs()", a))
                    }
                    "$min" if args.len() == 2 => {
                        let l = self.arith_to_expr(&args[0], bindings)?;
                        let r = self.arith_to_expr(&args[1], bindings)?;
                        Some(format!("({}).min({})", l, r))
                    }
                    "$max" if args.len() == 2 => {
                        let l = self.arith_to_expr(&args[0], bindings)?;
                        let r = self.arith_to_expr(&args[1], bindings)?;
                        Some(format!("({}).max({})", l, r))
                    }
                    "$mod" if args.len() == 2 => {
                        let l = self.arith_to_expr(&args[0], bindings)?;
                        let r = self.arith_to_expr(&args[1], bindings)?;
                        Some(format!("(({} as i64) % ({} as i64)) as f64", l, r))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Generate query methods
    fn generate_query_methods(&self) -> String {
        let mut code = String::new();

        for gen_struct in self.structs.values() {
            let fn_name = gen_struct.functor.to_lowercase();

            writeln!(code, "\n    /// Lookup value for {} item", fn_name).unwrap();
            writeln!(code, "    pub fn lookup_{}(&self, item: &{}) -> Option<{}> {{",
                fn_name, gen_struct.name, self.config.value_type
            ).unwrap();
            writeln!(code, "        self.{}_values.get(item).copied()", fn_name).unwrap();
            writeln!(code, "    }}").unwrap();

            writeln!(code, "\n    /// Get all {} items", fn_name).unwrap();
            writeln!(code, "    pub fn all_{}(&self) -> impl Iterator<Item = (&{}, &{})> {{",
                fn_name, gen_struct.name, self.config.value_type
            ).unwrap();
            writeln!(code, "        self.{}_values.iter()", fn_name).unwrap();
            writeln!(code, "    }}").unwrap();
        }

        code
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rule::Rule;
    use crate::term::Product;

    #[test]
    fn test_generate_transitive_closure() {
        // path(I, K) += edge(I, J) * path(J, K).
        // path(I, J) += edge(I, J).
        let rules = vec![
            Rule::new(
                Term::compound("path", vec![Term::var(0), Term::var(2)]),
                Product::new(vec![
                    Term::compound("edge", vec![Term::var(0), Term::var(1)]),
                    Term::compound("path", vec![Term::var(1), Term::var(2)]),
                ]),
            ),
            Rule::new(
                Term::compound("path", vec![Term::var(0), Term::var(1)]),
                Product::new(vec![
                    Term::compound("edge", vec![Term::var(0), Term::var(1)]),
                ]),
            ),
        ];

        let program = Program::from_rules(rules);
        let analysis = ProgramAnalysis::analyze(&program);
        let config = CodeGenConfig::counting();
        let generator = CodeGenerator::new(analysis, config);

        let code = generator.generate(&program);
        println!("{}", code);

        assert!(code.contains("struct Edge"));
        assert!(code.contains("struct Path"));
        assert!(code.contains("pub fn solve"));
    }

    #[test]
    fn test_generate_cky() {
        // phrase(X, I, K) += phrase(Y, I, J) * phrase(Z, J, K) * rewrite(X, Y, Z).
        let binary_rule = Rule::new(
            Term::compound("phrase", vec![Term::var(0), Term::var(3), Term::var(5)]),
            Product::new(vec![
                Term::compound("phrase", vec![Term::var(1), Term::var(3), Term::var(4)]),
                Term::compound("phrase", vec![Term::var(2), Term::var(4), Term::var(5)]),
                Term::compound("rewrite", vec![Term::var(0), Term::var(1), Term::var(2)]),
            ]),
        );

        let program = Program::from_rules(vec![binary_rule]);
        let analysis = ProgramAnalysis::analyze(&program);
        let config = CodeGenConfig::counting();
        let generator = CodeGenerator::new(analysis, config);

        let code = generator.generate(&program);
        println!("{}", code);

        // Check that structs are generated
        assert!(code.contains("struct Phrase"));
        assert!(code.contains("struct Rewrite"));

        // Check that indexes are generated
        assert!(code.contains("phrase_by_"));

        // Check that solver is generated
        assert!(code.contains("pub fn solve"));
    }
}
