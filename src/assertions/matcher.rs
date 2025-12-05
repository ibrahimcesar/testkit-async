// Allow must_use_candidate for matcher factory functions since returning the matcher
// without using it is the common pattern for test setup
#![allow(clippy::must_use_candidate)]

//! Custom matcher system for flexible assertions.
//!
//! This module provides a flexible matcher system for complex assertions:
//!
//! - [`Matcher`] trait for custom matchers
//! - Built-in matchers: [`eq`], [`gt`], [`lt`], [`contains`], etc.
//! - Combinators: [`all_of`], [`any_of`], [`not`]
//!
//! # Example
//!
//! ```rust
//! use testkit_async::assertions::matcher::{eq, gt, not, Matcher};
//!
//! // Single matchers
//! let m = eq(42);
//! assert!(m.matches(&42));
//!
//! // Combinators - use same matcher type or box them
//! let m = gt(0);
//! assert!(m.matches(&50));
//!
//! // Negation
//! let m = not(eq(0));
//! assert!(m.matches(&1));
//! ```

use std::fmt::Debug;

/// A matcher for testing values.
///
/// Matchers can be combined using [`all_of`], [`any_of`], and [`not`].
///
/// # Implementing Custom Matchers
///
/// ```rust
/// use testkit_async::assertions::matcher::Matcher;
///
/// struct IsEven;
///
/// impl Matcher<i32> for IsEven {
///     fn matches(&self, value: &i32) -> bool {
///         value % 2 == 0
///     }
///
///     fn describe(&self) -> String {
///         "is even".to_string()
///     }
///
///     fn describe_mismatch(&self, value: &i32) -> String {
///         format!("{} is not even", value)
///     }
/// }
///
/// let m = IsEven;
/// assert!(m.matches(&4));
/// assert!(!m.matches(&3));
/// ```
pub trait Matcher<T: ?Sized> {
    /// Check if the value matches.
    fn matches(&self, value: &T) -> bool;

    /// Describe what this matcher expects.
    fn describe(&self) -> String;

    /// Describe why a value didn't match.
    fn describe_mismatch(&self, value: &T) -> String;
}

/// Assert that a value matches a matcher.
///
/// # Panics
///
/// Panics with a descriptive message if the value doesn't match.
///
/// # Example
///
/// ```rust
/// use testkit_async::{assert_that, assertions::matcher::eq};
///
/// assert_that!(42, eq(42));
/// ```
#[macro_export]
macro_rules! assert_that {
    ($value:expr, $matcher:expr) => {{
        let value = &$value;
        let matcher = &$matcher;
        if !$crate::assertions::matcher::Matcher::matches(matcher, value) {
            panic!(
                "assertion failed: {}\n  expected: {}\n  got: {:?}",
                $crate::assertions::matcher::Matcher::describe_mismatch(matcher, value),
                $crate::assertions::matcher::Matcher::describe(matcher),
                value
            );
        }
    }};
    ($value:expr, $matcher:expr, $($arg:tt)+) => {{
        let value = &$value;
        let matcher = &$matcher;
        if !$crate::assertions::matcher::Matcher::matches(matcher, value) {
            panic!(
                "assertion failed: {}\n  expected: {}\n  got: {:?}\n  message: {}",
                $crate::assertions::matcher::Matcher::describe_mismatch(matcher, value),
                $crate::assertions::matcher::Matcher::describe(matcher),
                value,
                format_args!($($arg)+)
            );
        }
    }};
}

// =============================================================================
// Built-in Matchers
// =============================================================================

/// Create an equality matcher.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, eq};
///
/// let m = eq(42);
/// assert!(m.matches(&42));
/// assert!(!m.matches(&0));
/// ```
pub fn eq<T: PartialEq + Debug>(expected: T) -> EqMatcher<T> {
    EqMatcher { expected }
}

/// Matcher for equality.
pub struct EqMatcher<T> {
    expected: T,
}

impl<T: PartialEq + Debug> Matcher<T> for EqMatcher<T> {
    fn matches(&self, value: &T) -> bool {
        value == &self.expected
    }

    fn describe(&self) -> String {
        format!("equals {:?}", self.expected)
    }

    fn describe_mismatch(&self, value: &T) -> String {
        format!("{:?} does not equal {:?}", value, self.expected)
    }
}

/// Create a greater-than matcher.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, gt};
///
/// let m = gt(10);
/// assert!(m.matches(&20));
/// assert!(!m.matches(&5));
/// ```
pub fn gt<T: PartialOrd + Debug>(threshold: T) -> GtMatcher<T> {
    GtMatcher { threshold }
}

/// Matcher for greater-than comparison.
pub struct GtMatcher<T> {
    threshold: T,
}

impl<T: PartialOrd + Debug> Matcher<T> for GtMatcher<T> {
    fn matches(&self, value: &T) -> bool {
        value > &self.threshold
    }

    fn describe(&self) -> String {
        format!("is greater than {:?}", self.threshold)
    }

    fn describe_mismatch(&self, value: &T) -> String {
        format!("{:?} is not greater than {:?}", value, self.threshold)
    }
}

/// Create a greater-than-or-equal matcher.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, gte};
///
/// let m = gte(10);
/// assert!(m.matches(&10));
/// assert!(m.matches(&20));
/// assert!(!m.matches(&5));
/// ```
pub fn gte<T: PartialOrd + Debug>(threshold: T) -> GteMatcher<T> {
    GteMatcher { threshold }
}

/// Matcher for greater-than-or-equal comparison.
pub struct GteMatcher<T> {
    threshold: T,
}

impl<T: PartialOrd + Debug> Matcher<T> for GteMatcher<T> {
    fn matches(&self, value: &T) -> bool {
        value >= &self.threshold
    }

    fn describe(&self) -> String {
        format!("is greater than or equal to {:?}", self.threshold)
    }

    fn describe_mismatch(&self, value: &T) -> String {
        format!(
            "{:?} is not greater than or equal to {:?}",
            value, self.threshold
        )
    }
}

/// Create a less-than matcher.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, lt};
///
/// let m = lt(10);
/// assert!(m.matches(&5));
/// assert!(!m.matches(&20));
/// ```
pub fn lt<T: PartialOrd + Debug>(threshold: T) -> LtMatcher<T> {
    LtMatcher { threshold }
}

/// Matcher for less-than comparison.
pub struct LtMatcher<T> {
    threshold: T,
}

impl<T: PartialOrd + Debug> Matcher<T> for LtMatcher<T> {
    fn matches(&self, value: &T) -> bool {
        value < &self.threshold
    }

    fn describe(&self) -> String {
        format!("is less than {:?}", self.threshold)
    }

    fn describe_mismatch(&self, value: &T) -> String {
        format!("{:?} is not less than {:?}", value, self.threshold)
    }
}

/// Create a less-than-or-equal matcher.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, lte};
///
/// let m = lte(10);
/// assert!(m.matches(&10));
/// assert!(m.matches(&5));
/// assert!(!m.matches(&20));
/// ```
pub fn lte<T: PartialOrd + Debug>(threshold: T) -> LteMatcher<T> {
    LteMatcher { threshold }
}

/// Matcher for less-than-or-equal comparison.
pub struct LteMatcher<T> {
    threshold: T,
}

impl<T: PartialOrd + Debug> Matcher<T> for LteMatcher<T> {
    fn matches(&self, value: &T) -> bool {
        value <= &self.threshold
    }

    fn describe(&self) -> String {
        format!("is less than or equal to {:?}", self.threshold)
    }

    fn describe_mismatch(&self, value: &T) -> String {
        format!(
            "{:?} is not less than or equal to {:?}",
            value, self.threshold
        )
    }
}

/// Create a substring contains matcher for strings.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, contains_str};
///
/// let m = contains_str("world");
/// assert!(m.matches(&"hello world".to_string()));
/// assert!(!m.matches(&"hello".to_string()));
/// ```
pub fn contains_str(substring: &str) -> ContainsStrMatcher {
    ContainsStrMatcher {
        substring: substring.to_string(),
    }
}

/// Matcher for string contains.
pub struct ContainsStrMatcher {
    substring: String,
}

impl Matcher<String> for ContainsStrMatcher {
    fn matches(&self, value: &String) -> bool {
        value.contains(&self.substring)
    }

    fn describe(&self) -> String {
        format!("contains {:?}", self.substring)
    }

    fn describe_mismatch(&self, value: &String) -> String {
        format!("{:?} does not contain {:?}", value, self.substring)
    }
}

impl Matcher<str> for ContainsStrMatcher {
    fn matches(&self, value: &str) -> bool {
        value.contains(&self.substring)
    }

    fn describe(&self) -> String {
        format!("contains {:?}", self.substring)
    }

    fn describe_mismatch(&self, value: &str) -> String {
        format!("{:?} does not contain {:?}", value, self.substring)
    }
}

/// Create a starts-with matcher for strings.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, starts_with};
///
/// let m = starts_with("hello");
/// assert!(m.matches(&"hello world".to_string()));
/// assert!(!m.matches(&"world hello".to_string()));
/// ```
pub fn starts_with(prefix: &str) -> StartsWithMatcher {
    StartsWithMatcher {
        prefix: prefix.to_string(),
    }
}

/// Matcher for string starts-with.
pub struct StartsWithMatcher {
    prefix: String,
}

impl Matcher<String> for StartsWithMatcher {
    fn matches(&self, value: &String) -> bool {
        value.starts_with(&self.prefix)
    }

    fn describe(&self) -> String {
        format!("starts with {:?}", self.prefix)
    }

    fn describe_mismatch(&self, value: &String) -> String {
        format!("{:?} does not start with {:?}", value, self.prefix)
    }
}

impl Matcher<str> for StartsWithMatcher {
    fn matches(&self, value: &str) -> bool {
        value.starts_with(&self.prefix)
    }

    fn describe(&self) -> String {
        format!("starts with {:?}", self.prefix)
    }

    fn describe_mismatch(&self, value: &str) -> String {
        format!("{:?} does not start with {:?}", value, self.prefix)
    }
}

/// Create an ends-with matcher for strings.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, ends_with};
///
/// let m = ends_with("world");
/// assert!(m.matches(&"hello world".to_string()));
/// assert!(!m.matches(&"world hello".to_string()));
/// ```
pub fn ends_with(suffix: &str) -> EndsWithMatcher {
    EndsWithMatcher {
        suffix: suffix.to_string(),
    }
}

/// Matcher for string ends-with.
pub struct EndsWithMatcher {
    suffix: String,
}

impl Matcher<String> for EndsWithMatcher {
    fn matches(&self, value: &String) -> bool {
        value.ends_with(&self.suffix)
    }

    fn describe(&self) -> String {
        format!("ends with {:?}", self.suffix)
    }

    fn describe_mismatch(&self, value: &String) -> String {
        format!("{:?} does not end with {:?}", value, self.suffix)
    }
}

impl Matcher<str> for EndsWithMatcher {
    fn matches(&self, value: &str) -> bool {
        value.ends_with(&self.suffix)
    }

    fn describe(&self) -> String {
        format!("ends with {:?}", self.suffix)
    }

    fn describe_mismatch(&self, value: &str) -> String {
        format!("{:?} does not end with {:?}", value, self.suffix)
    }
}

/// Create a length matcher for collections.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, has_length};
///
/// let m = has_length(3);
/// assert!(m.matches(&vec![1, 2, 3]));
/// assert!(!m.matches(&vec![1, 2]));
/// ```
pub fn has_length<T>(len: usize) -> HasLengthMatcher<T> {
    HasLengthMatcher {
        length: len,
        _phantom: std::marker::PhantomData,
    }
}

/// Matcher for collection length.
pub struct HasLengthMatcher<T> {
    length: usize,
    _phantom: std::marker::PhantomData<T>,
}

impl<T: Debug> Matcher<Vec<T>> for HasLengthMatcher<T> {
    fn matches(&self, value: &Vec<T>) -> bool {
        value.len() == self.length
    }

    fn describe(&self) -> String {
        format!("has length {}", self.length)
    }

    fn describe_mismatch(&self, value: &Vec<T>) -> String {
        format!(
            "expected length {}, but was {} (value: {:?})",
            self.length,
            value.len(),
            value
        )
    }
}

impl<T: Debug> Matcher<[T]> for HasLengthMatcher<T> {
    fn matches(&self, value: &[T]) -> bool {
        value.len() == self.length
    }

    fn describe(&self) -> String {
        format!("has length {}", self.length)
    }

    fn describe_mismatch(&self, value: &[T]) -> String {
        format!(
            "expected length {}, but was {} (value: {:?})",
            self.length,
            value.len(),
            value
        )
    }
}

/// Create an is-empty matcher for collections.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, is_empty};
///
/// let m = is_empty::<i32>();
/// assert!(m.matches(&Vec::<i32>::new()));
/// assert!(!m.matches(&vec![1]));
/// ```
pub fn is_empty<T>() -> IsEmptyMatcher<T> {
    IsEmptyMatcher {
        _phantom: std::marker::PhantomData,
    }
}

/// Matcher for empty collections.
pub struct IsEmptyMatcher<T> {
    _phantom: std::marker::PhantomData<T>,
}

impl<T: Debug> Matcher<Vec<T>> for IsEmptyMatcher<T> {
    fn matches(&self, value: &Vec<T>) -> bool {
        value.is_empty()
    }

    fn describe(&self) -> String {
        "is empty".to_string()
    }

    fn describe_mismatch(&self, value: &Vec<T>) -> String {
        format!("expected empty, but had {} elements: {:?}", value.len(), value)
    }
}

impl<T: Debug> Matcher<[T]> for IsEmptyMatcher<T> {
    fn matches(&self, value: &[T]) -> bool {
        value.is_empty()
    }

    fn describe(&self) -> String {
        "is empty".to_string()
    }

    fn describe_mismatch(&self, value: &[T]) -> String {
        format!("expected empty, but had {} elements: {:?}", value.len(), value)
    }
}

/// Create a contains-element matcher for collections.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, contains};
///
/// let m = contains(2);
/// assert!(m.matches(&vec![1, 2, 3]));
/// assert!(!m.matches(&vec![1, 3]));
/// ```
pub fn contains<T: PartialEq + Debug>(element: T) -> ContainsMatcher<T> {
    ContainsMatcher { element }
}

/// Matcher for collection contains element.
pub struct ContainsMatcher<T> {
    element: T,
}

impl<T: PartialEq + Debug> Matcher<Vec<T>> for ContainsMatcher<T> {
    fn matches(&self, value: &Vec<T>) -> bool {
        value.contains(&self.element)
    }

    fn describe(&self) -> String {
        format!("contains {:?}", self.element)
    }

    fn describe_mismatch(&self, value: &Vec<T>) -> String {
        format!("{:?} does not contain {:?}", value, self.element)
    }
}

impl<T: PartialEq + Debug> Matcher<[T]> for ContainsMatcher<T> {
    fn matches(&self, value: &[T]) -> bool {
        value.contains(&self.element)
    }

    fn describe(&self) -> String {
        format!("contains {:?}", self.element)
    }

    fn describe_mismatch(&self, value: &[T]) -> String {
        format!("{:?} does not contain {:?}", value, self.element)
    }
}

/// Create a matcher that always matches.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, anything};
///
/// let m = anything::<i32>();
/// assert!(m.matches(&42));
/// assert!(m.matches(&0));
/// ```
pub fn anything<T>() -> AnythingMatcher<T> {
    AnythingMatcher {
        _phantom: std::marker::PhantomData,
    }
}

/// Matcher that matches anything.
pub struct AnythingMatcher<T> {
    _phantom: std::marker::PhantomData<T>,
}

impl<T: Debug> Matcher<T> for AnythingMatcher<T> {
    fn matches(&self, _value: &T) -> bool {
        true
    }

    fn describe(&self) -> String {
        "anything".to_string()
    }

    fn describe_mismatch(&self, _value: &T) -> String {
        // This should never be called since matches always returns true
        "matches anything".to_string()
    }
}

/// Create a predicate-based matcher.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, satisfies};
///
/// let m = satisfies(|x: &i32| *x % 2 == 0, "is even");
/// assert!(m.matches(&4));
/// assert!(!m.matches(&3));
/// ```
pub fn satisfies<T, F>(predicate: F, description: &str) -> PredicateMatcher<T, F>
where
    F: Fn(&T) -> bool,
{
    PredicateMatcher {
        predicate,
        description: description.to_string(),
        _phantom: std::marker::PhantomData,
    }
}

/// Matcher based on a predicate function.
pub struct PredicateMatcher<T, F> {
    predicate: F,
    description: String,
    _phantom: std::marker::PhantomData<T>,
}

impl<T: Debug, F: Fn(&T) -> bool> Matcher<T> for PredicateMatcher<T, F> {
    fn matches(&self, value: &T) -> bool {
        (self.predicate)(value)
    }

    fn describe(&self) -> String {
        self.description.clone()
    }

    fn describe_mismatch(&self, value: &T) -> String {
        format!("{:?} does not satisfy: {}", value, self.description)
    }
}

// =============================================================================
// Combinators
// =============================================================================

/// Create a matcher that matches when all matchers match.
///
/// Note: All matchers in the vector must be the same type. For different
/// matcher types, use [`all_of_boxed`] instead.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, all_of, gt};
///
/// // Use same matcher type
/// let m = all_of(vec![gt(0), gt(10), gt(20)]);
/// assert!(m.matches(&50));
/// assert!(!m.matches(&15));
/// ```
pub fn all_of<T, M>(matchers: Vec<M>) -> AllOfMatcher<T>
where
    M: Matcher<T> + 'static,
    T: Debug,
{
    AllOfMatcher {
        matchers: matchers
            .into_iter()
            .map(|m| Box::new(m) as Box<dyn Matcher<T>>)
            .collect(),
    }
}

/// Create a matcher from boxed matchers (for different types).
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, all_of_boxed, gt, lt};
///
/// // Different matcher types - box them first
/// let matchers: Vec<Box<dyn Matcher<i32>>> = vec![Box::new(gt(0)), Box::new(lt(100))];
/// let m = all_of_boxed(matchers);
/// assert!(m.matches(&50));
/// assert!(!m.matches(&0));
/// ```
pub fn all_of_boxed<T: Debug>(matchers: Vec<Box<dyn Matcher<T>>>) -> AllOfMatcher<T> {
    AllOfMatcher { matchers }
}

/// Matcher that requires all inner matchers to match.
pub struct AllOfMatcher<T: ?Sized> {
    matchers: Vec<Box<dyn Matcher<T>>>,
}

impl<T: Debug> Matcher<T> for AllOfMatcher<T> {
    fn matches(&self, value: &T) -> bool {
        self.matchers.iter().all(|m| m.matches(value))
    }

    fn describe(&self) -> String {
        let descriptions: Vec<_> = self.matchers.iter().map(|m| m.describe()).collect();
        format!("all of [{}]", descriptions.join(", "))
    }

    fn describe_mismatch(&self, value: &T) -> String {
        let failures: Vec<_> = self
            .matchers
            .iter()
            .filter(|m| !m.matches(value))
            .map(|m| m.describe_mismatch(value))
            .collect();
        format!("failed: {}", failures.join("; "))
    }
}

/// Create a matcher that matches when any matcher matches.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, any_of, eq};
///
/// let m = any_of(vec![eq(1), eq(2), eq(3)]);
/// assert!(m.matches(&2));
/// assert!(!m.matches(&4));
/// ```
pub fn any_of<T>(matchers: Vec<impl Matcher<T> + 'static>) -> AnyOfMatcher<T>
where
    T: Debug,
{
    AnyOfMatcher {
        matchers: matchers
            .into_iter()
            .map(|m| Box::new(m) as Box<dyn Matcher<T>>)
            .collect(),
    }
}

/// Matcher that requires at least one inner matcher to match.
pub struct AnyOfMatcher<T: ?Sized> {
    matchers: Vec<Box<dyn Matcher<T>>>,
}

impl<T: Debug> Matcher<T> for AnyOfMatcher<T> {
    fn matches(&self, value: &T) -> bool {
        self.matchers.iter().any(|m| m.matches(value))
    }

    fn describe(&self) -> String {
        let descriptions: Vec<_> = self.matchers.iter().map(|m| m.describe()).collect();
        format!("any of [{}]", descriptions.join(", "))
    }

    fn describe_mismatch(&self, value: &T) -> String {
        let descriptions: Vec<_> = self.matchers.iter().map(|m| m.describe()).collect();
        format!(
            "{:?} matched none of [{}]",
            value,
            descriptions.join(", ")
        )
    }
}

/// Create a negating matcher.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::matcher::{Matcher, not, eq};
///
/// let m = not(eq(0));
/// assert!(m.matches(&1));
/// assert!(!m.matches(&0));
/// ```
pub fn not<T, M: Matcher<T> + 'static>(matcher: M) -> NotMatcher<T> {
    NotMatcher {
        inner: Box::new(matcher),
    }
}

/// Matcher that negates another matcher.
pub struct NotMatcher<T: ?Sized> {
    inner: Box<dyn Matcher<T>>,
}

impl<T: Debug> Matcher<T> for NotMatcher<T> {
    fn matches(&self, value: &T) -> bool {
        !self.inner.matches(value)
    }

    fn describe(&self) -> String {
        format!("not {}", self.inner.describe())
    }

    fn describe_mismatch(&self, value: &T) -> String {
        format!("{:?} unexpectedly matched: {}", value, self.inner.describe())
    }
}

// Implement Matcher for Box<dyn Matcher> to allow nesting
impl<T: ?Sized> Matcher<T> for Box<dyn Matcher<T>> {
    fn matches(&self, value: &T) -> bool {
        (**self).matches(value)
    }

    fn describe(&self) -> String {
        (**self).describe()
    }

    fn describe_mismatch(&self, value: &T) -> String {
        (**self).describe_mismatch(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eq_matcher() {
        let m = eq(42);
        assert!(m.matches(&42));
        assert!(!m.matches(&0));
    }

    #[test]
    fn test_gt_matcher() {
        let m = gt(10);
        assert!(m.matches(&20));
        assert!(!m.matches(&10));
        assert!(!m.matches(&5));
    }

    #[test]
    fn test_gte_matcher() {
        let m = gte(10);
        assert!(m.matches(&20));
        assert!(m.matches(&10));
        assert!(!m.matches(&5));
    }

    #[test]
    fn test_lt_matcher() {
        let m = lt(10);
        assert!(m.matches(&5));
        assert!(!m.matches(&10));
        assert!(!m.matches(&20));
    }

    #[test]
    fn test_lte_matcher() {
        let m = lte(10);
        assert!(m.matches(&5));
        assert!(m.matches(&10));
        assert!(!m.matches(&20));
    }

    #[test]
    fn test_contains_str_matcher() {
        let m = contains_str("world");
        assert!(m.matches(&"hello world".to_string()));
        assert!(!m.matches(&"hello".to_string()));
    }

    #[test]
    fn test_starts_with_matcher() {
        let m = starts_with("hello");
        assert!(m.matches(&"hello world".to_string()));
        assert!(!m.matches(&"world hello".to_string()));
    }

    #[test]
    fn test_ends_with_matcher() {
        let m = ends_with("world");
        assert!(m.matches(&"hello world".to_string()));
        assert!(!m.matches(&"world hello".to_string()));
    }

    #[test]
    fn test_has_length_matcher() {
        let m = has_length::<i32>(3);
        assert!(m.matches(&vec![1, 2, 3]));
        assert!(!m.matches(&vec![1, 2]));
    }

    #[test]
    fn test_is_empty_matcher() {
        let m = is_empty::<i32>();
        assert!(m.matches(&Vec::<i32>::new()));
        assert!(!m.matches(&vec![1]));
    }

    #[test]
    fn test_contains_matcher() {
        let m = contains(2);
        assert!(m.matches(&vec![1, 2, 3]));
        assert!(!m.matches(&vec![1, 3]));
    }

    #[test]
    fn test_anything_matcher() {
        let m = anything::<i32>();
        assert!(m.matches(&42));
        assert!(m.matches(&0));
        assert!(m.matches(&-100));
    }

    #[test]
    fn test_satisfies_matcher() {
        let m = satisfies(|x: &i32| *x % 2 == 0, "is even");
        assert!(m.matches(&4));
        assert!(!m.matches(&3));
    }

    #[test]
    fn test_all_of_combinator() {
        let gt_matcher: Box<dyn Matcher<i32>> = Box::new(gt(0));
        let lt_matcher: Box<dyn Matcher<i32>> = Box::new(lt(100));
        let m = all_of(vec![gt_matcher, lt_matcher]);
        assert!(m.matches(&50));
        assert!(!m.matches(&0));
        assert!(!m.matches(&100));
    }

    #[test]
    fn test_any_of_combinator() {
        let m = any_of(vec![eq(1), eq(2), eq(3)]);
        assert!(m.matches(&1));
        assert!(m.matches(&2));
        assert!(m.matches(&3));
        assert!(!m.matches(&4));
    }

    #[test]
    fn test_not_combinator() {
        let m = not(eq(0));
        assert!(m.matches(&1));
        assert!(!m.matches(&0));
    }

    #[test]
    fn test_assert_that_macro() {
        assert_that!(42, eq(42));
        let gt_matcher: Box<dyn Matcher<i32>> = Box::new(gt(0));
        let lt_matcher: Box<dyn Matcher<i32>> = Box::new(lt(100));
        assert_that!(50, all_of(vec![gt_matcher, lt_matcher]));
        // Test with satisfies which only has one impl
        assert_that!("hello", satisfies(|s: &&str| s.contains("ell"), "contains 'ell'"));
    }

    #[test]
    #[should_panic(expected = "does not equal")]
    fn test_assert_that_fails() {
        assert_that!(42, eq(0));
    }

    #[test]
    fn test_matcher_describe() {
        assert_eq!(eq(42).describe(), "equals 42");
        assert_eq!(gt(10).describe(), "is greater than 10");
        assert_eq!(lt(10).describe(), "is less than 10");
        assert_eq!(
            <ContainsStrMatcher as Matcher<String>>::describe(&contains_str("x")),
            "contains \"x\""
        );
        assert_eq!(
            <HasLengthMatcher<i32> as Matcher<Vec<i32>>>::describe(&has_length::<i32>(3)),
            "has length 3"
        );
        assert_eq!(
            <IsEmptyMatcher<i32> as Matcher<Vec<i32>>>::describe(&is_empty::<i32>()),
            "is empty"
        );
        assert_eq!(not(eq(0)).describe(), "not equals 0");
    }

    #[test]
    fn test_matcher_describe_mismatch() {
        assert!(eq(42).describe_mismatch(&0).contains("does not equal"));
        assert!(gt(10).describe_mismatch(&5).contains("not greater than"));
        assert!(
            <ContainsStrMatcher as Matcher<String>>::describe_mismatch(
                &contains_str("x"),
                &"y".to_string()
            )
            .contains("does not contain")
        );
    }

    #[test]
    fn test_nested_combinators() {
        // (x > 0 AND x < 100) OR x == 200
        // We need to box the matchers manually for different types
        let inner1: Box<dyn Matcher<i32>> = Box::new(gt(0));
        let inner2: Box<dyn Matcher<i32>> = Box::new(lt(100));
        let all_matcher = all_of(vec![inner1, inner2]);

        let m1: Box<dyn Matcher<i32>> = Box::new(all_matcher);
        let m2: Box<dyn Matcher<i32>> = Box::new(eq(200));
        let m = any_of(vec![m1, m2]);

        assert!(m.matches(&50));
        assert!(m.matches(&200));
        assert!(!m.matches(&150));
    }
}
