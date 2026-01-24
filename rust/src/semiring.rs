//! Semiring trait and implementations for Dyna.
//!
//! Semirings provide the algebraic structure for combining values in Dyna programs.
//! Common semirings include:
//! - Float (real numbers with +, *)
//! - Boolean (or, and)
//! - MinPlus (tropical semiring)
//! - MaxTimes (Viterbi semiring)

use ordered_float::OrderedFloat;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::{Add, Mul};

/// A semiring provides addition (aggregation) and multiplication (combination) operations.
pub trait Semiring: Clone + Debug + Default + PartialEq + Add<Output = Self> + Mul<Output = Self> {
    /// The additive identity (zero element).
    fn zero() -> Self;

    /// The multiplicative identity (one element).
    fn one() -> Self;

    /// Check if this value is approximately equal to zero.
    fn is_zero(&self) -> bool;

    /// Check if two values are approximately equal.
    fn approx_eq(&self, other: &Self) -> bool;

    /// Kleene star operation (for solving linear recurrences).
    /// Default implementation panics; override for semirings that support it.
    fn star(&self) -> Self {
        panic!("Kleene star not supported for this semiring")
    }
}

/// Float semiring: real numbers with + and *.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Float(pub f64);

impl Float {
    pub fn new(x: f64) -> Self {
        Float(x)
    }

    pub fn value(&self) -> f64 {
        self.0
    }
}

impl Semiring for Float {
    fn zero() -> Self {
        Float(0.0)
    }

    fn one() -> Self {
        Float(1.0)
    }

    fn is_zero(&self) -> bool {
        self.0.abs() < 1e-10
    }

    fn approx_eq(&self, other: &Self) -> bool {
        (self.0 - other.0).abs() < 1e-10
    }

    fn star(&self) -> Self {
        // For |x| < 1: star(x) = 1 / (1 - x)
        if self.0.abs() >= 1.0 {
            panic!("Kleene star requires |x| < 1");
        }
        Float(1.0 / (1.0 - self.0))
    }
}

impl Add for Float {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Float(self.0 + other.0)
    }
}

impl Mul for Float {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Float(self.0 * other.0)
    }
}

impl From<f64> for Float {
    fn from(x: f64) -> Self {
        Float(x)
    }
}

impl From<Float> for f64 {
    fn from(x: Float) -> Self {
        x.0
    }
}

/// Boolean semiring: or and and.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Boolean(pub bool);

impl Boolean {
    pub fn new(x: bool) -> Self {
        Boolean(x)
    }

    pub fn value(&self) -> bool {
        self.0
    }
}

impl Semiring for Boolean {
    fn zero() -> Self {
        Boolean(false)
    }

    fn one() -> Self {
        Boolean(true)
    }

    fn is_zero(&self) -> bool {
        !self.0
    }

    fn approx_eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    fn star(&self) -> Self {
        Boolean(true)
    }
}

impl Add for Boolean {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Boolean(self.0 || other.0)
    }
}

impl Mul for Boolean {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Boolean(self.0 && other.0)
    }
}

impl From<bool> for Boolean {
    fn from(x: bool) -> Self {
        Boolean(x)
    }
}

/// MinPlus (tropical) semiring: min and +.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct MinPlus(pub OrderedFloat<f64>);

impl MinPlus {
    pub fn new(x: f64) -> Self {
        MinPlus(OrderedFloat(x))
    }

    pub fn infinity() -> Self {
        MinPlus(OrderedFloat(f64::INFINITY))
    }

    pub fn value(&self) -> f64 {
        self.0.into_inner()
    }
}

impl Semiring for MinPlus {
    fn zero() -> Self {
        MinPlus::infinity()
    }

    fn one() -> Self {
        MinPlus::new(0.0)
    }

    fn is_zero(&self) -> bool {
        self.0.is_infinite() && self.0.is_sign_positive()
    }

    fn approx_eq(&self, other: &Self) -> bool {
        (self.0.into_inner() - other.0.into_inner()).abs() < 1e-10
    }
}

impl Add for MinPlus {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        MinPlus(self.0.min(other.0))
    }
}

impl Mul for MinPlus {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        MinPlus(OrderedFloat(self.0.into_inner() + other.0.into_inner()))
    }
}

/// MaxTimes (Viterbi) semiring: max and *.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct MaxTimes(pub OrderedFloat<f64>);

impl MaxTimes {
    pub fn new(x: f64) -> Self {
        MaxTimes(OrderedFloat(x))
    }

    pub fn value(&self) -> f64 {
        self.0.into_inner()
    }
}

impl Semiring for MaxTimes {
    fn zero() -> Self {
        MaxTimes::new(0.0)
    }

    fn one() -> Self {
        MaxTimes::new(1.0)
    }

    fn is_zero(&self) -> bool {
        self.0.into_inner().abs() < 1e-10
    }

    fn approx_eq(&self, other: &Self) -> bool {
        (self.0.into_inner() - other.0.into_inner()).abs() < 1e-10
    }
}

impl Add for MaxTimes {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        MaxTimes(self.0.max(other.0))
    }
}

impl Mul for MaxTimes {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        MaxTimes(OrderedFloat(self.0.into_inner() * other.0.into_inner()))
    }
}

/// Counting semiring: natural numbers with + and *.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Count(pub u64);

impl Count {
    pub fn new(x: u64) -> Self {
        Count(x)
    }

    pub fn value(&self) -> u64 {
        self.0
    }
}

impl Semiring for Count {
    fn zero() -> Self {
        Count(0)
    }

    fn one() -> Self {
        Count(1)
    }

    fn is_zero(&self) -> bool {
        self.0 == 0
    }

    fn approx_eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Add for Count {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Count(self.0.saturating_add(other.0))
    }
}

impl Mul for Count {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Count(self.0.saturating_mul(other.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_float_semiring() {
        let a = Float::new(2.0);
        let b = Float::new(3.0);

        assert_eq!(a + b, Float::new(5.0));
        assert_eq!(a * b, Float::new(6.0));
        assert!(Float::zero().is_zero());
        assert!(!Float::one().is_zero());
    }

    #[test]
    fn test_float_star() {
        let x = Float::new(0.5);
        let star = x.star();
        assert!((star.0 - 2.0).abs() < 1e-10);
    }

    #[test]
    fn test_boolean_semiring() {
        assert_eq!(Boolean(true) + Boolean(false), Boolean(true));
        assert_eq!(Boolean(true) * Boolean(false), Boolean(false));
        assert_eq!(Boolean(false) + Boolean(false), Boolean(false));
        assert_eq!(Boolean(true) * Boolean(true), Boolean(true));
    }

    #[test]
    fn test_minplus_semiring() {
        let a = MinPlus::new(3.0);
        let b = MinPlus::new(5.0);

        // min(3, 5) = 3
        assert_eq!(a + b, MinPlus::new(3.0));
        // 3 + 5 = 8
        assert_eq!(a * b, MinPlus::new(8.0));

        // Identity elements
        assert_eq!(a + MinPlus::zero(), a);
        assert_eq!(a * MinPlus::one(), a);
    }

    #[test]
    fn test_maxtimes_semiring() {
        let a = MaxTimes::new(0.3);
        let b = MaxTimes::new(0.5);

        // max(0.3, 0.5) = 0.5
        assert_eq!(a + b, MaxTimes::new(0.5));
        // 0.3 * 0.5 = 0.15
        assert!((a * b).value() - 0.15 < 1e-10);
    }

    #[test]
    fn test_count_semiring() {
        let a = Count::new(3);
        let b = Count::new(4);

        assert_eq!(a + b, Count::new(7));
        assert_eq!(a * b, Count::new(12));
    }
}
