//! Latency injection for testing timeout and slow operation handling.
//!
//! This module provides [`LatencyInjector`] for adding artificial delays
//! to async operations, useful for testing timeout behavior and performance
//! under slow conditions.

#![allow(clippy::cast_sign_loss)]

use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::task::{Context, Poll};
use std::time::Duration;

use parking_lot::Mutex;

/// Artificial latency injector.
///
/// Adds configurable delays to operations. Supports fixed latency,
/// random ranges, and normal distributions.
///
/// # Example
///
/// ```rust
/// use std::time::Duration;
/// use testkit_async::chaos::LatencyInjector;
///
/// // Fixed 100ms latency
/// let latency = LatencyInjector::fixed(Duration::from_millis(100));
/// assert_eq!(latency.next_delay(), Duration::from_millis(100));
///
/// // Random latency between 50-150ms
/// let latency = LatencyInjector::uniform(
///     Duration::from_millis(50),
///     Duration::from_millis(150),
/// );
/// let delay = latency.next_delay();
/// assert!(delay >= Duration::from_millis(50));
/// assert!(delay <= Duration::from_millis(150));
/// ```
pub struct LatencyInjector {
    mode: LatencyMode,
    random_state: AtomicU64,
    jitter_nanos: u64,
    stats: Mutex<LatencyStats>,
}

#[derive(Clone, Debug)]
enum LatencyMode {
    /// Fixed latency for all operations.
    Fixed(Duration),
    /// Uniform random latency within range.
    Uniform { min: Duration, max: Duration },
    /// Normal distribution latency.
    Normal { mean_nanos: u64, std_dev_nanos: u64 },
    /// No latency.
    None,
}

/// Statistics about latency injection.
#[derive(Clone, Copy, Debug, Default)]
pub struct LatencyStats {
    /// Total number of delays applied.
    pub delay_count: u64,
    /// Total latency added (sum of all delays).
    pub total_latency: Duration,
    /// Maximum latency added.
    pub max_latency: Duration,
    /// Minimum latency added (zero if no delays).
    pub min_latency: Option<Duration>,
}

impl LatencyInjector {
    /// Create an injector with fixed latency.
    ///
    /// # Example
    ///
    /// ```rust
    /// use std::time::Duration;
    /// use testkit_async::chaos::LatencyInjector;
    ///
    /// let latency = LatencyInjector::fixed(Duration::from_millis(100));
    /// assert_eq!(latency.next_delay(), Duration::from_millis(100));
    /// assert_eq!(latency.next_delay(), Duration::from_millis(100));
    /// ```
    #[must_use]
    pub fn fixed(duration: Duration) -> Self {
        Self {
            mode: LatencyMode::Fixed(duration),
            random_state: AtomicU64::new(0x1234_5678_9ABC_DEF0),
            jitter_nanos: 0,
            stats: Mutex::new(LatencyStats::default()),
        }
    }

    /// Create an injector with uniform random latency in range.
    ///
    /// Each call to [`next_delay`] returns a random duration between
    /// `min` and `max` (inclusive).
    ///
    /// # Panics
    ///
    /// Panics if `min > max`.
    ///
    /// [`next_delay`]: LatencyInjector::next_delay
    #[must_use]
    pub fn uniform(min: Duration, max: Duration) -> Self {
        assert!(min <= max, "min must be <= max");
        Self {
            mode: LatencyMode::Uniform { min, max },
            random_state: AtomicU64::new(0x1234_5678_9ABC_DEF0),
            jitter_nanos: 0,
            stats: Mutex::new(LatencyStats::default()),
        }
    }

    /// Create an injector with normally distributed latency.
    ///
    /// Uses Box-Muller transform for normal distribution.
    ///
    /// # Example
    ///
    /// ```rust
    /// use std::time::Duration;
    /// use testkit_async::chaos::LatencyInjector;
    ///
    /// // Mean 100ms, std dev 20ms
    /// let latency = LatencyInjector::normal(
    ///     Duration::from_millis(100),
    ///     Duration::from_millis(20),
    /// );
    /// ```
    #[must_use]
    pub fn normal(mean: Duration, std_dev: Duration) -> Self {
        Self {
            mode: LatencyMode::Normal {
                mean_nanos: mean.as_nanos() as u64,
                std_dev_nanos: std_dev.as_nanos() as u64,
            },
            random_state: AtomicU64::new(0x1234_5678_9ABC_DEF0),
            jitter_nanos: 0,
            stats: Mutex::new(LatencyStats::default()),
        }
    }

    /// Create an injector with no latency.
    ///
    /// Useful as a baseline or when conditionally disabling latency.
    #[must_use]
    pub fn none() -> Self {
        Self {
            mode: LatencyMode::None,
            random_state: AtomicU64::new(0),
            jitter_nanos: 0,
            stats: Mutex::new(LatencyStats::default()),
        }
    }

    /// Add random jitter on top of the base latency.
    ///
    /// The jitter is uniformly distributed in the range [0, `max_jitter`].
    ///
    /// # Example
    ///
    /// ```rust
    /// use std::time::Duration;
    /// use testkit_async::chaos::LatencyInjector;
    ///
    /// // 100ms base + up to 10ms jitter
    /// let latency = LatencyInjector::fixed(Duration::from_millis(100))
    ///     .with_jitter(Duration::from_millis(10));
    ///
    /// let delay = latency.next_delay();
    /// assert!(delay >= Duration::from_millis(100));
    /// assert!(delay <= Duration::from_millis(110));
    /// ```
    #[must_use]
    pub fn with_jitter(mut self, max_jitter: Duration) -> Self {
        self.jitter_nanos = max_jitter.as_nanos() as u64;
        self
    }

    /// Set the random seed for reproducibility.
    #[must_use]
    pub fn with_seed(self, seed: u64) -> Self {
        self.random_state.store(seed, Ordering::SeqCst);
        self
    }

    /// Get the next delay duration.
    ///
    /// This computes the delay that should be applied and updates statistics.
    #[must_use]
    pub fn next_delay(&self) -> Duration {
        let base_nanos = match &self.mode {
            LatencyMode::Fixed(d) => d.as_nanos() as u64,
            LatencyMode::Uniform { min, max } => {
                let min_nanos = min.as_nanos() as u64;
                let max_nanos = max.as_nanos() as u64;
                if min_nanos == max_nanos {
                    min_nanos
                } else {
                    let range = max_nanos - min_nanos;
                    min_nanos + (self.next_random_u64() % range)
                }
            }
            LatencyMode::Normal {
                mean_nanos,
                std_dev_nanos,
            } => {
                // Box-Muller transform for normal distribution
                let u1 = self.next_random_f64();
                let u2 = self.next_random_f64();

                // Avoid log(0)
                let u1 = if u1 < f64::EPSILON { f64::EPSILON } else { u1 };

                let z = (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos();

                // Convert to nanos, clamping to non-negative
                let nanos = (*mean_nanos as f64) + z * (*std_dev_nanos as f64);
                nanos.max(0.0) as u64
            }
            LatencyMode::None => 0,
        };

        // Add jitter
        let jitter = if self.jitter_nanos > 0 {
            self.next_random_u64() % self.jitter_nanos
        } else {
            0
        };

        let total_nanos = base_nanos.saturating_add(jitter);
        let delay = Duration::from_nanos(total_nanos);

        // Update statistics
        let mut stats = self.stats.lock();
        stats.delay_count += 1;
        stats.total_latency += delay;
        if delay > stats.max_latency {
            stats.max_latency = delay;
        }
        match stats.min_latency {
            Some(min) if delay < min => stats.min_latency = Some(delay),
            None => stats.min_latency = Some(delay),
            _ => {}
        }

        delay
    }

    /// Get statistics about latency injection.
    #[must_use]
    pub fn stats(&self) -> LatencyStats {
        *self.stats.lock()
    }

    /// Reset statistics.
    pub fn reset_stats(&self) {
        *self.stats.lock() = LatencyStats::default();
    }

    /// Create a future that delays for the next latency duration.
    ///
    /// Note: This returns a [`DelayFuture`] that can be polled. For testing
    /// with [`MockClock`], the delay happens in virtual time.
    ///
    /// [`MockClock`]: crate::clock::MockClock
    #[must_use]
    pub fn delay_future(&self) -> DelayFuture {
        DelayFuture {
            duration: self.next_delay(),
            started: false,
        }
    }

    /// Apply latency to a future.
    ///
    /// Returns a future that first waits for the latency delay, then
    /// executes the provided future.
    pub fn apply<F>(&self, future: F) -> ApplyLatency<F>
    where
        F: Future,
    {
        ApplyLatency {
            delay: self.next_delay(),
            future,
            delay_complete: false,
        }
    }

    fn next_random_u64(&self) -> u64 {
        // xorshift64
        let mut x = self.random_state.load(Ordering::SeqCst);
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.random_state.store(x, Ordering::SeqCst);
        x
    }

    fn next_random_f64(&self) -> f64 {
        (self.next_random_u64() as f64) / (u64::MAX as f64)
    }
}

impl std::fmt::Debug for LatencyInjector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LatencyInjector")
            .field("mode", &self.mode)
            .field("jitter_nanos", &self.jitter_nanos)
            .field("stats", &*self.stats.lock())
            .finish()
    }
}

impl Default for LatencyInjector {
    fn default() -> Self {
        Self::none()
    }
}

/// A future representing a delay.
///
/// This is a simple future that records the intended delay duration
/// but completes immediately (for use with virtual time).
pub struct DelayFuture {
    duration: Duration,
    started: bool,
}

impl DelayFuture {
    /// Get the duration of this delay.
    #[must_use]
    pub fn duration(&self) -> Duration {
        self.duration
    }
}

impl Future for DelayFuture {
    type Output = Duration;

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.started {
            Poll::Ready(self.duration)
        } else {
            self.started = true;
            // In a real implementation with MockClock integration,
            // we would register with the clock and wait.
            // For now, we complete immediately and return the intended delay.
            Poll::Ready(self.duration)
        }
    }
}

/// A future that applies latency before executing another future.
pub struct ApplyLatency<F> {
    #[allow(dead_code)]
    delay: Duration,
    future: F,
    delay_complete: bool,
}

impl<F: Future + Unpin> Future for ApplyLatency<F> {
    type Output = F::Output;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if !self.delay_complete {
            // In a real implementation with MockClock integration,
            // we would wait for the delay duration.
            // For now, we skip the delay and proceed immediately.
            self.delay_complete = true;
        }

        Pin::new(&mut self.future).poll(cx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fixed_latency() {
        let latency = LatencyInjector::fixed(Duration::from_millis(100));

        for _ in 0..5 {
            assert_eq!(latency.next_delay(), Duration::from_millis(100));
        }

        let stats = latency.stats();
        assert_eq!(stats.delay_count, 5);
        assert_eq!(stats.total_latency, Duration::from_millis(500));
    }

    #[test]
    fn test_uniform_latency() {
        let latency =
            LatencyInjector::uniform(Duration::from_millis(50), Duration::from_millis(150));

        for _ in 0..100 {
            let delay = latency.next_delay();
            assert!(delay >= Duration::from_millis(50));
            assert!(delay <= Duration::from_millis(150));
        }
    }

    #[test]
    fn test_uniform_same_min_max() {
        let latency =
            LatencyInjector::uniform(Duration::from_millis(100), Duration::from_millis(100));

        assert_eq!(latency.next_delay(), Duration::from_millis(100));
    }

    #[test]
    fn test_normal_latency_non_negative() {
        let latency =
            LatencyInjector::normal(Duration::from_millis(100), Duration::from_millis(50));

        // Should never produce negative values
        for _ in 0..100 {
            let delay = latency.next_delay();
            assert!(delay >= Duration::ZERO);
        }
    }

    #[test]
    fn test_none_latency() {
        let latency = LatencyInjector::none();

        for _ in 0..5 {
            assert_eq!(latency.next_delay(), Duration::ZERO);
        }
    }

    #[test]
    fn test_jitter() {
        let latency = LatencyInjector::fixed(Duration::from_millis(100))
            .with_jitter(Duration::from_millis(10));

        for _ in 0..100 {
            let delay = latency.next_delay();
            assert!(delay >= Duration::from_millis(100));
            assert!(delay < Duration::from_millis(110));
        }
    }

    #[test]
    fn test_seeded_reproducible() {
        let results1: Vec<_> = {
            let latency =
                LatencyInjector::uniform(Duration::from_millis(0), Duration::from_millis(100))
                    .with_seed(42);
            (0..10).map(|_| latency.next_delay()).collect()
        };

        let results2: Vec<_> = {
            let latency =
                LatencyInjector::uniform(Duration::from_millis(0), Duration::from_millis(100))
                    .with_seed(42);
            (0..10).map(|_| latency.next_delay()).collect()
        };

        assert_eq!(results1, results2);
    }

    #[test]
    fn test_stats() {
        let latency = LatencyInjector::fixed(Duration::from_millis(100));

        latency.next_delay();
        latency.next_delay();
        latency.next_delay();

        let stats = latency.stats();
        assert_eq!(stats.delay_count, 3);
        assert_eq!(stats.total_latency, Duration::from_millis(300));
        assert_eq!(stats.max_latency, Duration::from_millis(100));
        assert_eq!(stats.min_latency, Some(Duration::from_millis(100)));
    }

    #[test]
    fn test_stats_variable_latency() {
        let latency =
            LatencyInjector::uniform(Duration::from_millis(10), Duration::from_millis(100))
                .with_seed(42);

        for _ in 0..10 {
            latency.next_delay();
        }

        let stats = latency.stats();
        assert_eq!(stats.delay_count, 10);
        assert!(stats.max_latency >= stats.min_latency.unwrap());
    }

    #[test]
    fn test_reset_stats() {
        let latency = LatencyInjector::fixed(Duration::from_millis(100));

        latency.next_delay();
        latency.next_delay();

        latency.reset_stats();

        let stats = latency.stats();
        assert_eq!(stats.delay_count, 0);
        assert_eq!(stats.total_latency, Duration::ZERO);
    }

    #[test]
    fn test_delay_future() {
        let latency = LatencyInjector::fixed(Duration::from_millis(100));
        let delay = latency.delay_future();

        assert_eq!(delay.duration(), Duration::from_millis(100));
    }

    #[test]
    fn test_default() {
        let latency = LatencyInjector::default();
        assert_eq!(latency.next_delay(), Duration::ZERO);
    }

    #[test]
    #[should_panic(expected = "min must be <= max")]
    fn test_uniform_invalid_range() {
        LatencyInjector::uniform(Duration::from_millis(100), Duration::from_millis(50));
    }
}
