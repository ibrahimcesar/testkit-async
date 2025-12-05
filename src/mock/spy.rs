// Allow must_use_candidate since spy methods often have useful side effects
#![allow(clippy::must_use_candidate)]

//! Test spy utilities for observing async function calls.
//!
//! This module provides [`Spy`] for wrapping functions and recording their calls.
//!
//! # Example
//!
//! ```rust
//! use testkit_async::mock::{Spy, SpyFn};
//!
//! // Create a spy wrapping a simple function
//! let spy = Spy::new(|x: i32| x * 2);
//!
//! // Call through the spy
//! let result = spy.call(5);
//! assert_eq!(result, 10);
//!
//! // Verify the call
//! assert!(spy.was_called());
//! assert_eq!(spy.call_count(), 1);
//! ```

use std::fmt::Debug;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use parking_lot::Mutex;

/// A record of a single function call.
#[derive(Debug, Clone)]
pub struct CallRecord<A, R> {
    /// The arguments passed to the call.
    pub args: A,
    /// The result returned by the call.
    pub result: R,
    /// Duration of the call.
    pub duration: Duration,
    /// When the call was made (relative to spy creation).
    pub timestamp: Duration,
}

/// A spy that wraps a function and records calls.
///
/// The spy wraps a callable and records each invocation, including
/// arguments, results, and timing information.
///
/// # Type Parameters
///
/// - `F` - The wrapped function type
/// - `A` - The argument type (must be Clone for recording)
/// - `R` - The return type (must be Clone for recording)
pub struct Spy<F, A, R> {
    inner: F,
    calls: Arc<Mutex<Vec<CallRecord<A, R>>>>,
    call_count: AtomicUsize,
    created_at: Instant,
}

impl<F, A, R> Spy<F, A, R>
where
    A: Clone,
    R: Clone,
{
    /// Create a new spy wrapping the given function.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::mock::Spy;
    ///
    /// let spy: Spy<_, i32, i32> = Spy::new(|x: i32| x + 1);
    /// ```
    pub fn new(func: F) -> Self {
        Self {
            inner: func,
            calls: Arc::new(Mutex::new(Vec::new())),
            call_count: AtomicUsize::new(0),
            created_at: Instant::now(),
        }
    }

    /// Get all recorded calls.
    pub fn calls(&self) -> Vec<CallRecord<A, R>> {
        self.calls.lock().clone()
    }

    /// Get the number of times the spy was called.
    #[must_use]
    pub fn call_count(&self) -> usize {
        self.call_count.load(Ordering::SeqCst)
    }

    /// Check if the spy was called at least once.
    #[must_use]
    pub fn was_called(&self) -> bool {
        self.call_count() > 0
    }

    /// Check if the spy was called exactly N times.
    #[must_use]
    pub fn was_called_times(&self, n: usize) -> bool {
        self.call_count() == n
    }

    /// Get the Nth call record (0-indexed).
    pub fn nth_call(&self, n: usize) -> Option<CallRecord<A, R>> {
        self.calls.lock().get(n).cloned()
    }

    /// Get the most recent call record.
    pub fn last_call(&self) -> Option<CallRecord<A, R>> {
        self.calls.lock().last().cloned()
    }

    /// Reset the call history.
    pub fn reset(&self) {
        self.calls.lock().clear();
        self.call_count.store(0, Ordering::SeqCst);
    }

    /// Record a call with the given arguments and result.
    fn record_call(&self, args: A, result: R, duration: Duration) {
        self.calls.lock().push(CallRecord {
            args,
            result,
            duration,
            timestamp: self.created_at.elapsed(),
        });
        self.call_count.fetch_add(1, Ordering::SeqCst);
    }
}

/// Trait for calling through a spy with specific argument/result types.
pub trait SpyFn<A, R> {
    /// Call the spied function with the given arguments.
    fn call(&self, args: A) -> R;
}

// Implementation for Fn(A) -> R
impl<F, A, R> SpyFn<A, R> for Spy<F, A, R>
where
    F: Fn(A) -> R,
    A: Clone,
    R: Clone,
{
    fn call(&self, args: A) -> R {
        let start = Instant::now();
        let result = (self.inner)(args.clone());
        let duration = start.elapsed();
        self.record_call(args, result.clone(), duration);
        result
    }
}

// Implementation for no-argument functions
impl<F, R> Spy<F, (), R>
where
    F: Fn() -> R,
    R: Clone,
{
    /// Call a no-argument function through the spy.
    pub fn call_no_args(&self) -> R {
        let start = Instant::now();
        let result = (self.inner)();
        let duration = start.elapsed();
        self.record_call((), result.clone(), duration);
        result
    }
}

impl<F, A, R> Clone for Spy<F, A, R>
where
    F: Clone,
    A: Clone,
    R: Clone,
{
    fn clone(&self) -> Self {
        // Note: Clone creates a new spy with the same function but independent state.
        // If you need shared state, use Arc<Spy<...>> instead.
        Self {
            inner: self.inner.clone(),
            calls: Arc::new(Mutex::new(self.calls.lock().clone())),
            call_count: AtomicUsize::new(self.call_count.load(Ordering::SeqCst)),
            created_at: self.created_at,
        }
    }
}

impl<F, A: Debug + Clone, R: Debug + Clone> Debug for Spy<F, A, R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Spy")
            .field("call_count", &self.call_count.load(Ordering::SeqCst))
            .field("calls", &*self.calls.lock())
            .finish()
    }
}

/// An async spy that wraps an async function and records calls.
///
/// Similar to [`Spy`] but for async functions.
pub struct AsyncSpy<F, A, R> {
    inner: F,
    calls: Arc<Mutex<Vec<CallRecord<A, R>>>>,
    call_count: AtomicUsize,
    created_at: Instant,
}

impl<F, A, R> AsyncSpy<F, A, R>
where
    A: Clone,
    R: Clone,
{
    /// Create a new async spy wrapping the given async function.
    pub fn new(func: F) -> Self {
        Self {
            inner: func,
            calls: Arc::new(Mutex::new(Vec::new())),
            call_count: AtomicUsize::new(0),
            created_at: Instant::now(),
        }
    }

    /// Get all recorded calls.
    pub fn calls(&self) -> Vec<CallRecord<A, R>> {
        self.calls.lock().clone()
    }

    /// Get the number of times the spy was called.
    #[must_use]
    pub fn call_count(&self) -> usize {
        self.call_count.load(Ordering::SeqCst)
    }

    /// Check if the spy was called at least once.
    #[must_use]
    pub fn was_called(&self) -> bool {
        self.call_count() > 0
    }

    /// Check if the spy was called exactly N times.
    #[must_use]
    pub fn was_called_times(&self, n: usize) -> bool {
        self.call_count() == n
    }

    /// Get the Nth call record (0-indexed).
    pub fn nth_call(&self, n: usize) -> Option<CallRecord<A, R>> {
        self.calls.lock().get(n).cloned()
    }

    /// Get the most recent call record.
    pub fn last_call(&self) -> Option<CallRecord<A, R>> {
        self.calls.lock().last().cloned()
    }

    /// Reset the call history.
    pub fn reset(&self) {
        self.calls.lock().clear();
        self.call_count.store(0, Ordering::SeqCst);
    }

    /// Record a call with the given arguments, result, and duration.
    pub fn record_call(&self, args: A, result: R, duration: Duration) {
        self.calls.lock().push(CallRecord {
            args,
            result,
            duration,
            timestamp: self.created_at.elapsed(),
        });
        self.call_count.fetch_add(1, Ordering::SeqCst);
    }
}

impl<F, A, R> Clone for AsyncSpy<F, A, R>
where
    F: Clone,
{
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            calls: Arc::clone(&self.calls),
            call_count: AtomicUsize::new(self.call_count.load(Ordering::SeqCst)),
            created_at: self.created_at,
        }
    }
}

impl<F, A: Debug + Clone, R: Debug + Clone> Debug for AsyncSpy<F, A, R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AsyncSpy")
            .field("call_count", &self.call_count.load(Ordering::SeqCst))
            .field("calls", &*self.calls.lock())
            .finish()
    }
}

/// Trait for calling through an async spy.
///
/// This trait can be implemented to provide async call functionality.
#[allow(dead_code)]
pub trait AsyncSpyFn<A, R> {
    /// The future type returned by the call.
    type Future: std::future::Future<Output = R>;

    /// Call the spied async function with the given arguments.
    fn call_async(&self, args: A) -> Self::Future;
}

/// A simple function spy that records call counts and arguments.
///
/// This is a simpler alternative when you just need to track calls
/// without wrapping an actual function.
pub struct CallTracker<A> {
    calls: Arc<Mutex<Vec<TrackedCall<A>>>>,
    call_count: AtomicUsize,
    created_at: Instant,
}

/// A tracked call record (just arguments and timing, no result).
#[derive(Debug, Clone)]
pub struct TrackedCall<A> {
    /// The arguments passed to the call.
    pub args: A,
    /// When the call was made (relative to tracker creation).
    pub timestamp: Duration,
}

impl<A: Clone> CallTracker<A> {
    /// Create a new call tracker.
    pub fn new() -> Self {
        Self {
            calls: Arc::new(Mutex::new(Vec::new())),
            call_count: AtomicUsize::new(0),
            created_at: Instant::now(),
        }
    }

    /// Record a call with the given arguments.
    pub fn track(&self, args: A) {
        self.calls.lock().push(TrackedCall {
            args,
            timestamp: self.created_at.elapsed(),
        });
        self.call_count.fetch_add(1, Ordering::SeqCst);
    }

    /// Get all tracked calls.
    pub fn calls(&self) -> Vec<TrackedCall<A>> {
        self.calls.lock().clone()
    }

    /// Get the number of tracked calls.
    #[must_use]
    pub fn call_count(&self) -> usize {
        self.call_count.load(Ordering::SeqCst)
    }

    /// Check if any calls were tracked.
    #[must_use]
    pub fn was_called(&self) -> bool {
        self.call_count() > 0
    }

    /// Check if called exactly N times.
    #[must_use]
    pub fn was_called_times(&self, n: usize) -> bool {
        self.call_count() == n
    }

    /// Get the Nth tracked call (0-indexed).
    pub fn nth_call(&self, n: usize) -> Option<TrackedCall<A>> {
        self.calls.lock().get(n).cloned()
    }

    /// Get the last tracked call.
    pub fn last_call(&self) -> Option<TrackedCall<A>> {
        self.calls.lock().last().cloned()
    }

    /// Check if called with a specific argument.
    pub fn was_called_with(&self, expected: &A) -> bool
    where
        A: PartialEq,
    {
        self.calls.lock().iter().any(|c| &c.args == expected)
    }

    /// Reset the tracker.
    pub fn reset(&self) {
        self.calls.lock().clear();
        self.call_count.store(0, Ordering::SeqCst);
    }
}

impl<A: Clone> Default for CallTracker<A> {
    fn default() -> Self {
        Self::new()
    }
}

impl<A: Clone> Clone for CallTracker<A> {
    fn clone(&self) -> Self {
        Self {
            calls: Arc::clone(&self.calls),
            call_count: AtomicUsize::new(self.call_count.load(Ordering::SeqCst)),
            created_at: self.created_at,
        }
    }
}

impl<A: Debug + Clone> Debug for CallTracker<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CallTracker")
            .field("call_count", &self.call_count.load(Ordering::SeqCst))
            .field("calls", &*self.calls.lock())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spy_basic() {
        let spy = Spy::new(|x: i32| x * 2);

        assert!(!spy.was_called());
        assert_eq!(spy.call_count(), 0);

        let result = spy.call(5);
        assert_eq!(result, 10);

        assert!(spy.was_called());
        assert_eq!(spy.call_count(), 1);
    }

    #[test]
    fn test_spy_multiple_calls() {
        let spy = Spy::new(|x: i32| x + 1);

        spy.call(1);
        spy.call(2);
        spy.call(3);

        assert_eq!(spy.call_count(), 3);
        assert!(spy.was_called_times(3));
    }

    #[test]
    fn test_spy_call_records() {
        let spy = Spy::new(|x: i32| x * x);

        spy.call(2);
        spy.call(3);
        spy.call(4);

        let calls = spy.calls();
        assert_eq!(calls.len(), 3);
        assert_eq!(calls[0].args, 2);
        assert_eq!(calls[0].result, 4);
        assert_eq!(calls[1].args, 3);
        assert_eq!(calls[1].result, 9);
        assert_eq!(calls[2].args, 4);
        assert_eq!(calls[2].result, 16);
    }

    #[test]
    fn test_spy_nth_call() {
        let spy = Spy::new(|x: i32| x);

        spy.call(10);
        spy.call(20);
        spy.call(30);

        assert_eq!(spy.nth_call(0).unwrap().args, 10);
        assert_eq!(spy.nth_call(1).unwrap().args, 20);
        assert_eq!(spy.nth_call(2).unwrap().args, 30);
        assert!(spy.nth_call(3).is_none());
    }

    #[test]
    fn test_spy_last_call() {
        let spy = Spy::new(|x: i32| x);

        assert!(spy.last_call().is_none());

        spy.call(1);
        assert_eq!(spy.last_call().unwrap().args, 1);

        spy.call(2);
        assert_eq!(spy.last_call().unwrap().args, 2);
    }

    #[test]
    fn test_spy_reset() {
        let spy = Spy::new(|x: i32| x);

        spy.call(1);
        spy.call(2);
        assert_eq!(spy.call_count(), 2);

        spy.reset();

        assert_eq!(spy.call_count(), 0);
        assert!(!spy.was_called());
        assert!(spy.calls().is_empty());
    }

    #[test]
    fn test_spy_no_args() {
        let spy = Spy::new(|| 42);

        let result = spy.call_no_args();
        assert_eq!(result, 42);

        assert!(spy.was_called());
    }

    #[test]
    fn test_spy_timing() {
        let spy = Spy::new(|_x: i32| {
            std::thread::sleep(Duration::from_millis(10));
            42
        });

        spy.call(1);

        let call = spy.nth_call(0).unwrap();
        assert!(call.duration >= Duration::from_millis(10));
    }

    #[test]
    fn test_call_tracker() {
        let tracker = CallTracker::<i32>::new();

        assert!(!tracker.was_called());

        tracker.track(1);
        tracker.track(2);
        tracker.track(3);

        assert!(tracker.was_called());
        assert_eq!(tracker.call_count(), 3);
    }

    #[test]
    fn test_call_tracker_was_called_with() {
        let tracker = CallTracker::new();

        tracker.track("hello");
        tracker.track("world");

        assert!(tracker.was_called_with(&"hello"));
        assert!(tracker.was_called_with(&"world"));
        assert!(!tracker.was_called_with(&"foo"));
    }

    #[test]
    fn test_call_tracker_reset() {
        let tracker = CallTracker::new();

        tracker.track(1);
        tracker.track(2);
        assert_eq!(tracker.call_count(), 2);

        tracker.reset();

        assert_eq!(tracker.call_count(), 0);
        assert!(tracker.calls().is_empty());
    }

    #[test]
    fn test_spy_debug() {
        let spy = Spy::new(|x: i32| x);
        spy.call(42);

        let debug = format!("{:?}", spy);
        assert!(debug.contains("Spy"));
        assert!(debug.contains("call_count"));
    }

    #[test]
    fn test_call_tracker_debug() {
        let tracker = CallTracker::new();
        tracker.track(42);

        let debug = format!("{:?}", tracker);
        assert!(debug.contains("CallTracker"));
        assert!(debug.contains("call_count"));
    }

    #[test]
    fn test_spy_clone_independent_state() {
        let spy1 = Spy::new(|x: i32| x);
        let spy2 = spy1.clone();

        spy1.call(1);
        spy2.call(2);

        // Clones have independent state
        assert_eq!(spy1.call_count(), 1);
        assert_eq!(spy2.call_count(), 1);
        assert_eq!(spy1.last_call().unwrap().args, 1);
        assert_eq!(spy2.last_call().unwrap().args, 2);
    }
}
