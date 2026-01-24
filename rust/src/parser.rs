//! Dyna syntax parser.
//!
//! This module provides a parser for Dyna syntax strings, producing Rust
//! Term, Rule, and Program objects. This allows tests and users to write
//! programs using readable Dyna syntax instead of manually constructing
//! Term objects.
//!
//! # Example
//!
//! ```rust
//! use dyna_rust::parser::parse_program;
//!
//! let program = parse_program(r#"
//!     path(X, Y) += edge(X, Y).
//!     path(X, Z) += edge(X, Y) * path(Y, Z).
//! "#).unwrap();
//!
//! assert_eq!(program.len(), 2);
//! ```

use crate::rule::{Program, Rule};
use crate::term::{Product, Term, Value, VarId};
use rustc_hash::FxHashMap;
use std::iter::Peekable;
use std::str::Chars;
use thiserror::Error;

/// Parser error type.
#[derive(Error, Debug, Clone, PartialEq)]
pub enum ParseError {
    #[error("unexpected end of input")]
    UnexpectedEof,
    #[error("unexpected character: {0}")]
    UnexpectedChar(char),
    #[error("expected {expected}, found {found}")]
    Expected { expected: String, found: String },
    #[error("invalid number: {0}")]
    InvalidNumber(String),
    #[error("unterminated string")]
    UnterminatedString,
}

/// Result type for parsing operations.
pub type ParseResult<T> = Result<T, ParseError>;

/// Token types for the lexer.
#[derive(Debug, Clone, PartialEq)]
enum Token {
    // Identifiers
    Var(String),      // Uppercase: X, Y, Foo
    Functor(String),  // Lowercase: edge, path, foo_bar

    // Literals
    Int(i64),
    Float(f64),
    String(String),

    // Keywords/Symbols
    LParen,      // (
    RParen,      // )
    LBracket,    // [
    RBracket,    // ]
    Comma,       // ,
    Dot,         // .
    Star,        // *
    Plus,        // +
    Minus,       // -
    PlusEq,      // +=
    ColonDash,   // :-
    Underscore,  // _ (anonymous var)
    Pipe,        // |

    Eof,
}

/// Lexer for Dyna syntax.
struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
    position: usize,
    /// Pending token to return (used when we consume a char but need to return it later)
    pending: Option<Token>,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        Lexer {
            input: input.chars().peekable(),
            position: 0,
            pending: None,
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.input.peek().copied()
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.input.next();
        if c.is_some() {
            self.position += 1;
        }
        c
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.advance();
            } else if c == '%' {
                // Skip comment to end of line
                while let Some(c) = self.peek() {
                    self.advance();
                    if c == '\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn read_while<F: Fn(char) -> bool>(&mut self, predicate: F) -> String {
        let mut result = String::new();
        while let Some(c) = self.peek() {
            if predicate(c) {
                result.push(c);
                self.advance();
            } else {
                break;
            }
        }
        result
    }

    fn read_string(&mut self) -> ParseResult<String> {
        // Consume opening quote
        self.advance();
        let mut result = String::new();
        loop {
            match self.advance() {
                Some('"') => return Ok(result),
                Some('\\') => {
                    // Handle escape sequences
                    match self.advance() {
                        Some('n') => result.push('\n'),
                        Some('t') => result.push('\t'),
                        Some('r') => result.push('\r'),
                        Some('"') => result.push('"'),
                        Some('\\') => result.push('\\'),
                        Some(c) => result.push(c),
                        None => return Err(ParseError::UnterminatedString),
                    }
                }
                Some(c) => result.push(c),
                None => return Err(ParseError::UnterminatedString),
            }
        }
    }

    fn read_number(&mut self, first: char) -> ParseResult<Token> {
        let mut s = String::new();
        s.push(first);

        // Read integer part
        s.push_str(&self.read_while(|c| c.is_ascii_digit()));

        // Check for decimal point
        if self.peek() == Some('.') {
            // Look ahead to see if it's a decimal or end of rule
            let pos = self.position;
            self.advance();
            if let Some(c) = self.peek() {
                if c.is_ascii_digit() {
                    s.push('.');
                    s.push_str(&self.read_while(|c| c.is_ascii_digit()));
                } else {
                    // It's the end-of-rule dot, not part of the number
                    // We already consumed the dot, so save it as a pending token
                    let n = s.parse::<i64>()
                        .map_err(|_| ParseError::InvalidNumber(s.clone()))?;
                    // Store the dot as pending so it's returned next
                    self.pending = Some(Token::Dot);
                    return Ok(Token::Int(n));
                }
            }
        }

        // Check for exponent
        if let Some(c) = self.peek() {
            if c == 'e' || c == 'E' {
                s.push(c);
                self.advance();
                if let Some(sign) = self.peek() {
                    if sign == '+' || sign == '-' {
                        s.push(sign);
                        self.advance();
                    }
                }
                s.push_str(&self.read_while(|c| c.is_ascii_digit()));
            }
        }

        // Parse as float if it has decimal point or exponent
        if s.contains('.') || s.contains('e') || s.contains('E') {
            let f = s.parse::<f64>()
                .map_err(|_| ParseError::InvalidNumber(s))?;
            Ok(Token::Float(f))
        } else {
            let n = s.parse::<i64>()
                .map_err(|_| ParseError::InvalidNumber(s))?;
            Ok(Token::Int(n))
        }
    }

    fn next_token(&mut self) -> ParseResult<Token> {
        // Return pending token if we have one
        if let Some(token) = self.pending.take() {
            return Ok(token);
        }

        self.skip_whitespace();

        match self.peek() {
            None => Ok(Token::Eof),
            Some(c) => {
                match c {
                    '(' => { self.advance(); Ok(Token::LParen) }
                    ')' => { self.advance(); Ok(Token::RParen) }
                    '[' => { self.advance(); Ok(Token::LBracket) }
                    ']' => { self.advance(); Ok(Token::RBracket) }
                    ',' => { self.advance(); Ok(Token::Comma) }
                    '.' => { self.advance(); Ok(Token::Dot) }
                    '*' => { self.advance(); Ok(Token::Star) }
                    '|' => { self.advance(); Ok(Token::Pipe) }
                    '_' => {
                        self.advance();
                        // Check if it's just _ or _Name
                        if let Some(c) = self.peek() {
                            if c.is_alphanumeric() || c == '_' {
                                let rest = self.read_while(|c| c.is_alphanumeric() || c == '_');
                                Ok(Token::Var(format!("_{}", rest)))
                            } else {
                                Ok(Token::Underscore)
                            }
                        } else {
                            Ok(Token::Underscore)
                        }
                    }
                    '+' => {
                        self.advance();
                        if self.peek() == Some('=') {
                            self.advance();
                            Ok(Token::PlusEq)
                        } else {
                            Ok(Token::Plus)
                        }
                    }
                    '-' => {
                        self.advance();
                        // Check if it's a negative number
                        if let Some(c) = self.peek() {
                            if c.is_ascii_digit() {
                                return self.read_number('-');
                            }
                        }
                        Ok(Token::Minus)
                    }
                    ':' => {
                        self.advance();
                        if self.peek() == Some('-') {
                            self.advance();
                            Ok(Token::ColonDash)
                        } else {
                            Err(ParseError::UnexpectedChar(':'))
                        }
                    }
                    '"' => {
                        let s = self.read_string()?;
                        Ok(Token::String(s))
                    }
                    c if c.is_ascii_digit() => {
                        self.advance();
                        self.read_number(c)
                    }
                    c if c.is_ascii_uppercase() || c == '$' => {
                        let name = self.read_while(|c| c.is_alphanumeric() || c == '_' || c == '\'');
                        Ok(Token::Var(name))
                    }
                    c if c.is_ascii_lowercase() => {
                        let name = self.read_while(|c| c.is_alphanumeric() || c == '_' || c == '\'');
                        // Check for keywords
                        match name.as_str() {
                            "true" => Ok(Token::Functor("true".to_string())),
                            "false" => Ok(Token::Functor("false".to_string())),
                            "inf" => Ok(Token::Float(f64::INFINITY)),
                            _ => Ok(Token::Functor(name)),
                        }
                    }
                    '\'' => {
                        // Single-quoted functor
                        self.advance();
                        let name = self.read_while(|c| c != '\'');
                        if self.peek() == Some('\'') {
                            self.advance();
                        }
                        Ok(Token::Functor(name))
                    }
                    c => Err(ParseError::UnexpectedChar(c)),
                }
            }
        }
    }
}

/// Parser for Dyna syntax.
pub struct Parser<'a> {
    lexer: Lexer<'a>,
    current: Token,
    var_map: FxHashMap<String, VarId>,
    next_var: VarId,
    anon_counter: u32,
}

impl<'a> Parser<'a> {
    /// Create a new parser for the given input.
    pub fn new(input: &'a str) -> ParseResult<Self> {
        let mut lexer = Lexer::new(input);
        let current = lexer.next_token()?;
        Ok(Parser {
            lexer,
            current,
            var_map: FxHashMap::default(),
            next_var: 0,
            anon_counter: 0,
        })
    }

    fn advance(&mut self) -> ParseResult<Token> {
        let prev = std::mem::replace(&mut self.current, self.lexer.next_token()?);
        Ok(prev)
    }

    fn expect(&mut self, expected: Token) -> ParseResult<()> {
        if self.current == expected {
            self.advance()?;
            Ok(())
        } else {
            Err(ParseError::Expected {
                expected: format!("{:?}", expected),
                found: format!("{:?}", self.current),
            })
        }
    }

    fn get_or_create_var(&mut self, name: &str) -> VarId {
        if let Some(&id) = self.var_map.get(name) {
            id
        } else {
            let id = self.next_var;
            self.next_var += 1;
            self.var_map.insert(name.to_string(), id);
            id
        }
    }

    fn fresh_anon_var(&mut self) -> VarId {
        self.anon_counter += 1;
        let name = format!("$Anon{}", self.anon_counter);
        self.get_or_create_var(&name)
    }

    /// Reset variable mappings for a new rule.
    fn reset_vars(&mut self) {
        self.var_map.clear();
        self.next_var = 0;
        self.anon_counter = 0;
    }

    /// Parse a term.
    fn parse_term(&mut self) -> ParseResult<Term> {
        match &self.current {
            Token::Var(name) => {
                let name = name.clone();
                self.advance()?;
                let id = self.get_or_create_var(&name);
                Ok(Term::Var(id))
            }
            Token::Underscore => {
                self.advance()?;
                let id = self.fresh_anon_var();
                Ok(Term::Var(id))
            }
            Token::Int(n) => {
                let n = *n;
                self.advance()?;
                Ok(Term::Const(Value::Int(n)))
            }
            Token::Float(f) => {
                let f = *f;
                self.advance()?;
                Ok(Term::Const(Value::Float(ordered_float::OrderedFloat(f))))
            }
            Token::String(s) => {
                let s = s.clone();
                self.advance()?;
                Ok(Term::Const(Value::Str(s.into())))
            }
            Token::Functor(name) => {
                let name = name.clone();
                self.advance()?;

                // Check for true/false literals
                if name == "true" {
                    return Ok(Term::Const(Value::Bool(true)));
                }
                if name == "false" {
                    return Ok(Term::Const(Value::Bool(false)));
                }

                // Check if it's a compound term with arguments
                if self.current == Token::LParen {
                    self.advance()?;
                    let mut args = Vec::new();

                    if self.current != Token::RParen {
                        args.push(self.parse_term()?);
                        while self.current == Token::Comma {
                            self.advance()?;
                            args.push(self.parse_term()?);
                        }
                    }

                    self.expect(Token::RParen)?;
                    Ok(Term::Compound {
                        functor: name.into(),
                        args,
                    })
                } else {
                    // Atom (0-arity compound term)
                    Ok(Term::Compound {
                        functor: name.into(),
                        args: Vec::new(),
                    })
                }
            }
            Token::LBracket => {
                // List syntax: [a, b, c] or [a, b | Rest]
                self.advance()?;
                let mut elements = Vec::new();
                let mut tail = None;

                if self.current != Token::RBracket {
                    elements.push(self.parse_term()?);

                    while self.current == Token::Comma {
                        self.advance()?;
                        elements.push(self.parse_term()?);
                    }

                    if self.current == Token::Pipe {
                        self.advance()?;
                        tail = Some(Box::new(self.parse_term()?));
                    }
                }

                self.expect(Token::RBracket)?;

                // Build list from elements
                let mut list = tail.map_or_else(
                    || Term::Compound { functor: "$nil".into(), args: Vec::new() },
                    |t| *t
                );

                for elem in elements.into_iter().rev() {
                    list = Term::Compound {
                        functor: "$cons".into(),
                        args: vec![elem, list],
                    };
                }

                Ok(list)
            }
            Token::LParen => {
                // Parenthesized expression
                self.advance()?;
                let term = self.parse_term()?;
                self.expect(Token::RParen)?;
                Ok(term)
            }
            _ => Err(ParseError::Expected {
                expected: "term".to_string(),
                found: format!("{:?}", self.current),
            }),
        }
    }

    /// Parse a rule body (product of terms).
    fn parse_body(&mut self) -> ParseResult<Product> {
        let mut terms = Vec::new();
        terms.push(self.parse_term()?);

        while self.current == Token::Star {
            self.advance()?;
            terms.push(self.parse_term()?);
        }

        // Also support comma as conjunction (common in Prolog/Dyna)
        while self.current == Token::Comma {
            self.advance()?;
            terms.push(self.parse_term()?);
        }

        Ok(Product::new(terms))
    }

    /// Parse a single rule.
    fn parse_rule(&mut self) -> ParseResult<Rule> {
        self.reset_vars();

        let head = self.parse_term()?;

        let body = match &self.current {
            Token::PlusEq => {
                self.advance()?;
                self.parse_body()?
            }
            Token::ColonDash => {
                self.advance()?;
                self.parse_body()?
            }
            Token::Dot => {
                // Fact - empty body
                Product::empty()
            }
            _ => {
                return Err(ParseError::Expected {
                    expected: "+=, :-, or .".to_string(),
                    found: format!("{:?}", self.current),
                });
            }
        };

        self.expect(Token::Dot)?;

        Ok(Rule::new(head, body))
    }

    /// Parse multiple rules into a program.
    pub fn parse_program(&mut self) -> ParseResult<Program> {
        let mut rules = Vec::new();

        while self.current != Token::Eof {
            rules.push(self.parse_rule()?);
        }

        Ok(Program::from_rules(rules))
    }
}

/// Parse a Dyna program from a string.
pub fn parse_program(input: &str) -> ParseResult<Program> {
    let mut parser = Parser::new(input)?;
    parser.parse_program()
}

/// Parse a single rule from a string.
pub fn parse_rule(input: &str) -> ParseResult<Rule> {
    let mut parser = Parser::new(input)?;
    parser.parse_rule()
}

/// Parse a single term from a string.
pub fn parse_term(input: &str) -> ParseResult<Term> {
    let mut parser = Parser::new(input)?;
    parser.parse_term()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_term_var() {
        let term = parse_term("X").unwrap();
        assert!(term.is_var());
    }

    #[test]
    fn test_parse_term_int() {
        let term = parse_term("42").unwrap();
        assert_eq!(term, Term::Const(Value::Int(42)));
    }

    #[test]
    fn test_parse_term_negative_int() {
        let term = parse_term("-123").unwrap();
        assert_eq!(term, Term::Const(Value::Int(-123)));
    }

    #[test]
    fn test_parse_term_float() {
        let term = parse_term("3.14").unwrap();
        if let Term::Const(Value::Float(f)) = term {
            assert!((f.into_inner() - 3.14).abs() < 0.001);
        } else {
            panic!("Expected float");
        }
    }

    #[test]
    fn test_parse_term_string() {
        let term = parse_term("\"hello\"").unwrap();
        assert_eq!(term, Term::Const(Value::Str("hello".into())));
    }

    #[test]
    fn test_parse_term_atom() {
        let term = parse_term("foo").unwrap();
        assert_eq!(term.functor(), Some("foo"));
        assert_eq!(term.arity(), 0);
    }

    #[test]
    fn test_parse_term_compound() {
        let term = parse_term("edge(1, 2)").unwrap();
        assert_eq!(term.functor(), Some("edge"));
        assert_eq!(term.arity(), 2);
    }

    #[test]
    fn test_parse_term_nested() {
        let term = parse_term("f(g(X), h(Y, Z))").unwrap();
        assert_eq!(term.functor(), Some("f"));
        assert_eq!(term.arity(), 2);
    }

    #[test]
    fn test_parse_fact() {
        let rule = parse_rule("edge(1, 2).").unwrap();
        assert!(rule.is_fact());
        assert_eq!(rule.head.functor(), Some("edge"));
    }

    #[test]
    fn test_parse_rule_plus_eq() {
        let rule = parse_rule("path(X, Y) += edge(X, Y).").unwrap();
        assert_eq!(rule.head.functor(), Some("path"));
        assert_eq!(rule.body.len(), 1);
    }

    #[test]
    fn test_parse_rule_colon_dash() {
        let rule = parse_rule("path(X, Y) :- edge(X, Y).").unwrap();
        assert_eq!(rule.head.functor(), Some("path"));
        assert_eq!(rule.body.len(), 1);
    }

    #[test]
    fn test_parse_rule_multiple_subgoals() {
        let rule = parse_rule("path(X, Z) += edge(X, Y) * path(Y, Z).").unwrap();
        assert_eq!(rule.head.functor(), Some("path"));
        assert_eq!(rule.body.len(), 2);
    }

    #[test]
    fn test_parse_program() {
        let program = parse_program(r#"
            path(X, Y) += edge(X, Y).
            path(X, Z) += edge(X, Y) * path(Y, Z).
        "#).unwrap();
        assert_eq!(program.len(), 2);
    }

    #[test]
    fn test_parse_program_cky() {
        let program = parse_program(r#"
            phrase(X, I, K) += phrase(Y, I, J) * phrase(Z, J, K) * rewrite(X, Y, Z).
        "#).unwrap();
        assert_eq!(program.len(), 1);
        let rule = program.get(0).unwrap();
        assert_eq!(rule.head.functor(), Some("phrase"));
        assert_eq!(rule.body.len(), 3);
    }

    #[test]
    fn test_parse_anonymous_var() {
        let rule = parse_rule("foo(X, _) += bar(X, _).").unwrap();
        // Each _ should be a different variable
        let vars = rule.vars();
        assert!(vars.len() >= 2); // X plus at least one anonymous var
    }

    #[test]
    fn test_parse_list() {
        let term = parse_term("[1, 2, 3]").unwrap();
        assert_eq!(term.functor(), Some("$cons"));
    }

    #[test]
    fn test_parse_list_with_tail() {
        let term = parse_term("[1, 2 | Rest]").unwrap();
        assert_eq!(term.functor(), Some("$cons"));
    }

    #[test]
    fn test_parse_empty_list() {
        let term = parse_term("[]").unwrap();
        assert_eq!(term.functor(), Some("$nil"));
    }

    #[test]
    fn test_parse_bool_literals() {
        let t = parse_term("true").unwrap();
        assert_eq!(t, Term::Const(Value::Bool(true)));

        let f = parse_term("false").unwrap();
        assert_eq!(f, Term::Const(Value::Bool(false)));
    }

    #[test]
    fn test_parse_with_comments() {
        let program = parse_program(r#"
            % This is a comment
            edge(1, 2).  % inline comment
            edge(2, 3).
        "#).unwrap();
        assert_eq!(program.len(), 2);
    }

    #[test]
    fn test_variable_reuse() {
        let rule = parse_rule("path(X, Z) += edge(X, Y) * path(Y, Z).").unwrap();
        // X appears twice, Y appears twice, Z appears twice
        // Should have 3 unique variables
        let vars = rule.vars();
        assert_eq!(vars.len(), 3);
    }

    #[test]
    fn test_parse_atoms() {
        let program = parse_program(r#"
            rewrite('S', 'NP', 'VP').
            rewrite(s, np, vp).
        "#).unwrap();
        assert_eq!(program.len(), 2);
    }
}
