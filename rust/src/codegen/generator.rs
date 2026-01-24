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
            ArgType::Term { .. } | ArgType::Any => {
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
    fn generate_indexes(&mut self) {
        for ((functor, arity), sig) in &self.analysis.functors {
            let struct_name = self.functor_to_struct_name(functor);

            for mode in &sig.modes {
                if mode.is_empty() {
                    continue; // No index needed for mode []
                }

                let index_name = format!("{}_by_{}",
                    functor.to_lowercase(),
                    mode.iter().map(|i| format!("arg{}", i)).collect::<Vec<_>>().join("_")
                );

                let key_fields: Vec<String> = mode.iter()
                    .map(|&i| format!("arg{}", i))
                    .collect();

                let key_types: Vec<RustType> = mode.iter()
                    .map(|&i| RustType::from_arg_type(&sig.arg_types[i], &self.config))
                    .collect();

                // Check if we can use array indexing
                let (use_array, bounds) = self.check_array_bounds(&sig.arg_types, mode);

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
        writeln!(code, "        }}").unwrap();
        writeln!(code, "    }}").unwrap();

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
                let sg_struct = self.structs.get(&(functor.clone(), args.len()));
                if let Some(sg_struct) = sg_struct {
                    // Find bound positions (where we have a binding)
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
                        // Find matching index
                        let index = self.indexes.iter().find(|idx|
                            idx.item_struct == sg_struct.name &&
                            idx.key_fields.len() == bound_positions.len()
                        );

                        if let Some(index) = index {
                            let key_exprs: Vec<String> = bound_positions.iter()
                                .map(|&i| {
                                    if let Term::Var(v) = &args[i] {
                                        bindings.get(v).cloned()
                                            .unwrap_or_else(|| format!("/* unbound {} */", v))
                                    } else {
                                        format!("/* const at {} */", i)
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
                                    key_exprs[0].clone()
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
                            // Fallback: iterate over all
                            writeln!(code, "{}for (&{}, &{}) in &self.{}_values {{",
                                current_indent, iter_var, val_var, functor.to_lowercase()
                            ).unwrap();
                            open_braces.push("for");
                            current_indent.push_str("    ");
                        }
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
                // Compute value expression
                let mut value_terms = vec!["delta".to_string()];
                for (idx, _) in rule.body.iter().enumerate() {
                    if idx != trigger_idx {
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
                        if let Term::Var(v) = arg {
                            bindings.get(v)
                                .map(|s| format!("{} as {}", s, head_struct.fields[i].1.type_name()))
                                .unwrap_or_else(|| format!("/* unbound {} */", v))
                        } else if let Term::Const(c) = arg {
                            match c {
                                Value::Int(n) => format!("{} as {}", n, head_struct.fields[i].1.type_name()),
                                Value::Symbol(s) => format!("/* symbol {} */", s),
                                _ => "/* const */".to_string(),
                            }
                        } else {
                            "/* complex */".to_string()
                        }
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
