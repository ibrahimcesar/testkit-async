//! Core failure injection traits and implementations.
//!
//! This module provides the foundational [`FailureInjector`] trait and several
//! implementations for common failure patterns.

use std::sync::atomic::{AtomicU64, Ordering};

use parking_lot::Mutex;

/// Statistics about injection attempts.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct InjectorStats {
    /// Total number of attempts recorded.
    pub attempts: u64,
    /// Number of times failure was triggered.
    pub failures: u64,
    /// Number of successful (non-failed) operations.
    pub successes: u64,
}

/// Core trait for failure injection.
///
/// Implementors decide when operations should fail and track statistics.
///
/// # Example
///
/// ```rust
/// use testkit_async::chaos::{FailureInjector, CountingInjector};
///
/// let injector = CountingInjector::fail_first(2);
///
/// // Simulate retrying an operation
/// for attempt in 0..5 {
///     if injector.should_fail() {
///         println!("Attempt {attempt} failed");
///     } else {
///         println!("Attempt {attempt} succeeded");
///     }
///     injector.record_attempt();
/// }
///
/// assert_eq!(injector.stats().failures, 2);
/// assert_eq!(injector.stats().successes, 3);
/// ```
pub trait FailureInjector: Send + Sync {
    /// Check if the next operation should fail.
    ///
    /// This should be called before attempting the operation.
    fn should_fail(&self) -> bool;

    /// Record that an attempt was made.
    ///
    /// Call this after each operation (whether it succeeded or failed).
    fn record_attempt(&self);

    /// Get current statistics.
    fn stats(&self) -> InjectorStats;

    /// Reset the injector to its initial state.
    fn reset(&self);
}

/// A failure injector based on call count.
///
/// Can be configured to fail:
/// - The first N calls
/// - Every Nth call
/// - After N successful calls
///
/// # Example
///
/// ```rust
/// use testkit_async::chaos::{FailureInjector, CountingInjector};
///
/// // Fail the first 3 calls
/// let injector = CountingInjector::fail_first(3);
///
/// assert!(injector.should_fail());
/// injector.record_attempt();
/// assert!(injector.should_fail());
/// injector.record_attempt();
/// assert!(injector.should_fail());
/// injector.record_attempt();
/// assert!(!injector.should_fail()); // 4th call succeeds
/// ```
pub struct CountingInjector {
    mode: CountingMode,
    count: AtomicU64,
    stats: Mutex<InjectorStats>,
}

#[derive(Clone, Copy, Debug)]
enum CountingMode {
    /// Fail the first N attempts.
    First(u64),
    /// Fail every Nth attempt (1-indexed).
    Every(u64),
    /// Fail after N successful attempts.
    After(u64),
}

impl CountingInjector {
    /// Create an injector that fails the first N attempts.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::chaos::{FailureInjector, CountingInjector};
    ///
    /// let injector = CountingInjector::fail_first(2);
    ///
    /// // First two fail
    /// assert!(injector.should_fail());
    /// injector.record_attempt();
    /// assert!(injector.should_fail());
    /// injector.record_attempt();
    ///
    /// // Third succeeds
    /// assert!(!injector.should_fail());
    /// ```
    #[must_use]
    pub fn fail_first(n: u64) -> Self {
        Self {
            mode: CountingMode::First(n),
            count: AtomicU64::new(0),
            stats: Mutex::new(InjectorStats::default()),
        }
    }

    /// Create an injector that fails every Nth attempt.
    ///
    /// Uses 1-based indexing: `fail_every(3)` fails attempts 3, 6, 9, etc.
    ///
    /// # Panics
    ///
    /// Panics if `n` is 0.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::chaos::{FailureInjector, CountingInjector};
    ///
    /// let injector = CountingInjector::fail_every(3);
    ///
    /// // 1, 2 succeed; 3 fails
    /// assert!(!injector.should_fail());
    /// injector.record_attempt();
    /// assert!(!injector.should_fail());
    /// injector.record_attempt();
    /// assert!(injector.should_fail());
    /// injector.record_attempt();
    ///
    /// // 4, 5 succeed; 6 fails
    /// assert!(!injector.should_fail());
    /// injector.record_attempt();
    /// assert!(!injector.should_fail());
    /// injector.record_attempt();
    /// assert!(injector.should_fail());
    /// ```
    #[must_use]
    pub fn fail_every(n: u64) -> Self {
        assert!(n > 0, "fail_every requires n > 0");
        Self {
            mode: CountingMode::Every(n),
            count: AtomicU64::new(0),
            stats: Mutex::new(InjectorStats::default()),
        }
    }

    /// Create an injector that fails after N successful attempts.
    ///
    /// The first N attempts succeed, then all subsequent attempts fail.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::chaos::{FailureInjector, CountingInjector};
    ///
    /// let injector = CountingInjector::fail_after(2);
    ///
    /// // First two succeed
    /// assert!(!injector.should_fail());
    /// injector.record_attempt();
    /// assert!(!injector.should_fail());
    /// injector.record_attempt();
    ///
    /// // Third and onwards fail
    /// assert!(injector.should_fail());
    /// ```
    #[must_use]
    pub fn fail_after(n: u64) -> Self {
        Self {
            mode: CountingMode::After(n),
            count: AtomicU64::new(0),
            stats: Mutex::new(InjectorStats::default()),
        }
    }

    /// Returns the current attempt count.
    #[must_use]
    pub fn attempt_count(&self) -> u64 {
        self.count.load(Ordering::SeqCst)
    }
}

impl FailureInjector for CountingInjector {
    fn should_fail(&self) -> bool {
        let current = self.count.load(Ordering::SeqCst);

        let fails = match self.mode {
            CountingMode::First(n) => current < n,
            CountingMode::Every(n) => (current + 1) % n == 0,
            CountingMode::After(n) => current >= n,
        };

        // Update stats
        let mut stats = self.stats.lock();
        if fails {
            stats.failures += 1;
        } else {
            stats.successes += 1;
        }

        fails
    }

    fn record_attempt(&self) {
        self.count.fetch_add(1, Ordering::SeqCst);
        self.stats.lock().attempts += 1;
    }

    fn stats(&self) -> InjectorStats {
        *self.stats.lock()
    }

    fn reset(&self) {
        self.count.store(0, Ordering::SeqCst);
        *self.stats.lock() = InjectorStats::default();
    }
}

impl std::fmt::Debug for CountingInjector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CountingInjector")
            .field("mode", &self.mode)
            .field("count", &self.count.load(Ordering::Relaxed))
            .field("stats", &*self.stats.lock())
            .finish()
    }
}

/// A failure injector based on probability.
///
/// Each call to `should_fail()` has a random chance of returning true.
///
/// # Example
///
/// ```rust
/// use testkit_async::chaos::{FailureInjector, ProbabilisticInjector};
///
/// // 50% chance of failure
/// let injector = ProbabilisticInjector::new(0.5);
///
/// // Run many attempts
/// for _ in 0..100 {
///     let _failed = injector.should_fail();
///     injector.record_attempt();
/// }
///
/// // With 100 attempts at 50%, we expect roughly 50 failures
/// let stats = injector.stats();
/// assert!(stats.failures > 20 && stats.failures < 80);
/// ```
pub struct ProbabilisticInjector {
    probability: f64,
    /// Seeded PRNG state for reproducibility.
    random_state: AtomicU64,
    stats: Mutex<InjectorStats>,
}

impl ProbabilisticInjector {
    /// Create an injector with the given failure probability.
    ///
    /// # Panics
    ///
    /// Panics if probability is not in the range [0.0, 1.0].
    #[must_use]
    pub fn new(probability: f64) -> Self {
        assert!(
            (0.0..=1.0).contains(&probability),
            "probability must be between 0.0 and 1.0"
        );
        Self {
            probability,
            random_state: AtomicU64::new(0x1234_5678_9ABC_DEF0),
            stats: Mutex::new(InjectorStats::default()),
        }
    }

    /// Create an injector with a specific seed for reproducibility.
    ///
    /// # Panics
    ///
    /// Panics if probability is not in the range [0.0, 1.0].
    #[must_use]
    pub fn with_seed(probability: f64, seed: u64) -> Self {
        assert!(
            (0.0..=1.0).contains(&probability),
            "probability must be between 0.0 and 1.0"
        );
        Self {
            probability,
            random_state: AtomicU64::new(seed),
            stats: Mutex::new(InjectorStats::default()),
        }
    }

    /// Returns the configured probability.
    #[must_use]
    pub fn probability(&self) -> f64 {
        self.probability
    }

    /// Generate a random number using xorshift.
    #[allow(clippy::cast_precision_loss)]
    fn next_random(&self) -> f64 {
        // xorshift64
        let mut x = self.random_state.load(Ordering::SeqCst);
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.random_state.store(x, Ordering::SeqCst);

        // Convert to [0.0, 1.0)
        (x as f64) / (u64::MAX as f64)
    }
}

impl FailureInjector for ProbabilisticInjector {
    fn should_fail(&self) -> bool {
        let fails = self.next_random() < self.probability;

        let mut stats = self.stats.lock();
        if fails {
            stats.failures += 1;
        } else {
            stats.successes += 1;
        }

        fails
    }

    fn record_attempt(&self) {
        self.stats.lock().attempts += 1;
    }

    fn stats(&self) -> InjectorStats {
        *self.stats.lock()
    }

    fn reset(&self) {
        *self.stats.lock() = InjectorStats::default();
    }
}

impl std::fmt::Debug for ProbabilisticInjector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ProbabilisticInjector")
            .field("probability", &self.probability)
            .field("stats", &*self.stats.lock())
            .finish_non_exhaustive()
    }
}

/// A failure injector that follows a predefined sequence.
///
/// Useful for testing specific failure patterns.
///
/// # Example
///
/// ```rust
/// use testkit_async::chaos::{FailureInjector, SequenceInjector};
///
/// // Fail, succeed, fail, succeed pattern
/// let injector = SequenceInjector::new(vec![true, false, true, false]);
///
/// assert!(injector.should_fail());
/// injector.record_attempt();
/// assert!(!injector.should_fail());
/// injector.record_attempt();
/// assert!(injector.should_fail());
/// injector.record_attempt();
/// assert!(!injector.should_fail());
/// ```
pub struct SequenceInjector {
    sequence: Vec<bool>,
    index: AtomicU64,
    loop_sequence: bool,
    stats: Mutex<InjectorStats>,
}

impl SequenceInjector {
    /// Create an injector with a fixed sequence.
    ///
    /// When the sequence is exhausted, all calls succeed.
    #[must_use]
    pub fn new(sequence: Vec<bool>) -> Self {
        Self {
            sequence,
            index: AtomicU64::new(0),
            loop_sequence: false,
            stats: Mutex::new(InjectorStats::default()),
        }
    }

    /// Create an injector that loops the sequence forever.
    #[must_use]
    pub fn looping(sequence: Vec<bool>) -> Self {
        Self {
            sequence,
            index: AtomicU64::new(0),
            loop_sequence: true,
            stats: Mutex::new(InjectorStats::default()),
        }
    }

    /// Returns the current position in the sequence.
    #[must_use]
    #[allow(clippy::cast_possible_truncation)]
    pub fn current_index(&self) -> usize {
        self.index.load(Ordering::SeqCst) as usize
    }
}

impl FailureInjector for SequenceInjector {
    #[allow(clippy::cast_possible_truncation)]
    fn should_fail(&self) -> bool {
        let idx = self.index.load(Ordering::SeqCst) as usize;

        let fails = if self.loop_sequence && !self.sequence.is_empty() {
            self.sequence[idx % self.sequence.len()]
        } else {
            self.sequence.get(idx).copied().unwrap_or(false)
        };

        let mut stats = self.stats.lock();
        if fails {
            stats.failures += 1;
        } else {
            stats.successes += 1;
        }

        fails
    }

    fn record_attempt(&self) {
        self.index.fetch_add(1, Ordering::SeqCst);
        self.stats.lock().attempts += 1;
    }

    fn stats(&self) -> InjectorStats {
        *self.stats.lock()
    }

    fn reset(&self) {
        self.index.store(0, Ordering::SeqCst);
        *self.stats.lock() = InjectorStats::default();
    }
}

impl std::fmt::Debug for SequenceInjector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SequenceInjector")
            .field("sequence", &self.sequence)
            .field("index", &self.index.load(Ordering::Relaxed))
            .field("loop_sequence", &self.loop_sequence)
            .field("stats", &*self.stats.lock())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_injector_stats_default() {
        let stats = InjectorStats::default();
        assert_eq!(stats.attempts, 0);
        assert_eq!(stats.failures, 0);
        assert_eq!(stats.successes, 0);
    }

    // CountingInjector tests

    #[test]
    fn test_counting_fail_first() {
        let injector = CountingInjector::fail_first(3);

        // First 3 fail
        for i in 0..3 {
            assert!(injector.should_fail(), "attempt {i} should fail");
            injector.record_attempt();
        }

        // Rest succeed
        for i in 3..6 {
            assert!(!injector.should_fail(), "attempt {i} should succeed");
            injector.record_attempt();
        }

        let stats = injector.stats();
        assert_eq!(stats.attempts, 6);
        assert_eq!(stats.failures, 3);
        assert_eq!(stats.successes, 3);
    }

    #[test]
    fn test_counting_fail_every() {
        let injector = CountingInjector::fail_every(3);

        let expected = [false, false, true, false, false, true, false, false, true];

        for (i, &should_fail) in expected.iter().enumerate() {
            assert_eq!(
                injector.should_fail(),
                should_fail,
                "attempt {i} should_fail mismatch"
            );
            injector.record_attempt();
        }

        let stats = injector.stats();
        assert_eq!(stats.failures, 3);
        assert_eq!(stats.successes, 6);
    }

    #[test]
    fn test_counting_fail_after() {
        let injector = CountingInjector::fail_after(2);

        // First 2 succeed
        assert!(!injector.should_fail());
        injector.record_attempt();
        assert!(!injector.should_fail());
        injector.record_attempt();

        // Rest fail
        for _ in 0..3 {
            assert!(injector.should_fail());
            injector.record_attempt();
        }

        let stats = injector.stats();
        assert_eq!(stats.attempts, 5);
        assert_eq!(stats.successes, 2);
        assert_eq!(stats.failures, 3);
    }

    #[test]
    fn test_counting_reset() {
        let injector = CountingInjector::fail_first(1);

        assert!(injector.should_fail());
        injector.record_attempt();
        assert!(!injector.should_fail());
        injector.record_attempt();

        injector.reset();

        // After reset, first call fails again
        assert!(injector.should_fail());
        injector.record_attempt();

        let stats = injector.stats();
        assert_eq!(stats.attempts, 1);
        assert_eq!(stats.failures, 1);
    }

    #[test]
    fn test_counting_attempt_count() {
        let injector = CountingInjector::fail_first(0);

        assert_eq!(injector.attempt_count(), 0);
        injector.record_attempt();
        assert_eq!(injector.attempt_count(), 1);
        injector.record_attempt();
        assert_eq!(injector.attempt_count(), 2);
    }

    // ProbabilisticInjector tests

    #[test]
    fn test_probabilistic_zero() {
        let injector = ProbabilisticInjector::new(0.0);

        for _ in 0..100 {
            assert!(!injector.should_fail());
            injector.record_attempt();
        }

        assert_eq!(injector.stats().failures, 0);
    }

    #[test]
    fn test_probabilistic_one() {
        let injector = ProbabilisticInjector::new(1.0);

        for _ in 0..100 {
            assert!(injector.should_fail());
            injector.record_attempt();
        }

        assert_eq!(injector.stats().successes, 0);
    }

    #[test]
    fn test_probabilistic_seeded_reproducible() {
        let results1: Vec<_> = {
            let injector = ProbabilisticInjector::with_seed(0.5, 42);
            (0..10)
                .map(|_| {
                    let result = injector.should_fail();
                    injector.record_attempt();
                    result
                })
                .collect()
        };

        let results2: Vec<_> = {
            let injector = ProbabilisticInjector::with_seed(0.5, 42);
            (0..10)
                .map(|_| {
                    let result = injector.should_fail();
                    injector.record_attempt();
                    result
                })
                .collect()
        };

        assert_eq!(results1, results2);
    }

    #[test]
    fn test_probabilistic_probability() {
        let injector = ProbabilisticInjector::new(0.75);
        assert!((injector.probability() - 0.75).abs() < f64::EPSILON);
    }

    #[test]
    #[should_panic(expected = "probability must be between 0.0 and 1.0")]
    fn test_probabilistic_invalid_high() {
        ProbabilisticInjector::new(1.5);
    }

    #[test]
    #[should_panic(expected = "probability must be between 0.0 and 1.0")]
    fn test_probabilistic_invalid_negative() {
        ProbabilisticInjector::new(-0.1);
    }

    // SequenceInjector tests

    #[test]
    fn test_sequence_basic() {
        let injector = SequenceInjector::new(vec![true, false, true]);

        assert!(injector.should_fail());
        injector.record_attempt();
        assert!(!injector.should_fail());
        injector.record_attempt();
        assert!(injector.should_fail());
        injector.record_attempt();

        // After sequence exhausted, defaults to success
        assert!(!injector.should_fail());
    }

    #[test]
    fn test_sequence_looping() {
        let injector = SequenceInjector::looping(vec![true, false]);

        let expected = [true, false, true, false, true, false];

        for (i, &expected_fail) in expected.iter().enumerate() {
            assert_eq!(
                injector.should_fail(),
                expected_fail,
                "iteration {i} mismatch"
            );
            injector.record_attempt();
        }
    }

    #[test]
    fn test_sequence_empty() {
        let injector = SequenceInjector::new(vec![]);

        // Empty sequence means never fail
        assert!(!injector.should_fail());
    }

    #[test]
    fn test_sequence_looping_empty() {
        let injector = SequenceInjector::looping(vec![]);

        // Empty looping sequence means never fail
        assert!(!injector.should_fail());
    }

    #[test]
    fn test_sequence_reset() {
        let injector = SequenceInjector::new(vec![true, false]);

        assert!(injector.should_fail());
        injector.record_attempt();

        injector.reset();

        assert!(injector.should_fail()); // Back to beginning
        assert_eq!(injector.current_index(), 0);
    }

    #[test]
    fn test_sequence_current_index() {
        let injector = SequenceInjector::new(vec![true, false, true]);

        assert_eq!(injector.current_index(), 0);
        injector.record_attempt();
        assert_eq!(injector.current_index(), 1);
        injector.record_attempt();
        assert_eq!(injector.current_index(), 2);
    }
}
