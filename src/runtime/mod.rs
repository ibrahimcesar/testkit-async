//! Runtime-agnostic abstractions for async testing.
//!
//! This module provides traits that abstract over different async runtimes,
//! allowing testkit-async to work with Tokio, async-std, smol, or any other
//! runtime without coupling to a specific implementation.
//!
//! # Core Traits
//!
//! - [`TimeSource`] - Abstraction over time operations (now, sleep)
//! - [`Spawner`] - Abstraction over task spawning
//! - [`Runtime`] - Combined runtime abstraction
//!
//! # Example
//!
//! ```rust,ignore
//! use testkit_async::runtime::{TimeSource, Spawner};
//!
//! // Use MockClock as a TimeSource
//! let clock = MockClock::new();
//! let now = clock.now();
//! clock.sleep(Duration::from_secs(1)).await;
//! ```

use std::future::Future;
use std::pin::Pin;
use std::time::Duration;

/// A source of time for async operations.
///
/// This trait abstracts over different time implementations, allowing
/// code to work with both real time and mock time.
///
/// # Implementations
///
/// - [`MockClock`](crate::clock::MockClock) - Mock time for testing
/// - `TokioTime` - Real tokio time (with `tokio` feature)
/// - `AsyncStdTime` - Real async-std time (with `async-std` feature)
pub trait TimeSource: Send + Sync {
    /// Get the current time as a duration since an epoch.
    fn now(&self) -> Duration;

    /// Create a future that completes after the given duration.
    fn sleep(&self, duration: Duration) -> Pin<Box<dyn Future<Output = ()> + Send + '_>>;

    /// Create a future that completes at the given instant.
    fn sleep_until(&self, deadline: Duration) -> Pin<Box<dyn Future<Output = ()> + Send + '_>> {
        let now = self.now();
        if deadline <= now {
            Box::pin(std::future::ready(()))
        } else {
            self.sleep(deadline - now)
        }
    }
}

/// A handle to a spawned task.
pub trait TaskJoinHandle: Send {
    /// The output type of the task.
    type Output;

    /// Wait for the task to complete and return its result.
    fn join(self) -> Pin<Box<dyn Future<Output = Option<Self::Output>> + Send>>;

    /// Abort the task.
    fn abort(&self);

    /// Check if the task is finished.
    fn is_finished(&self) -> bool;
}

/// A spawner for async tasks.
///
/// This trait abstracts over different task spawning mechanisms.
pub trait Spawner: Send + Sync {
    /// The join handle type for spawned tasks.
    type JoinHandle<T: Send + 'static>: TaskJoinHandle<Output = T> + Send;

    /// Spawn a new task.
    fn spawn<F, T>(&self, future: F) -> Self::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static;

    /// Spawn a new task with a name (for debugging).
    fn spawn_named<F, T>(&self, name: &str, future: F) -> Self::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        let _ = name; // Default implementation ignores name
        self.spawn(future)
    }
}

/// A complete async runtime abstraction.
///
/// Combines time and spawning capabilities.
pub trait Runtime: TimeSource + Spawner {
    /// Block on a future until it completes.
    fn block_on<F: Future>(&self, future: F) -> F::Output;
}

/// Configuration for runtime behavior.
#[derive(Debug, Clone, Default)]
pub struct RuntimeConfig {
    /// Whether to start with time paused (for mock time).
    pub start_paused: bool,
    /// Initial time offset.
    pub start_time: Option<Duration>,
    /// Enable deterministic task ordering.
    pub deterministic: bool,
}

impl RuntimeConfig {
    /// Create a new default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Start with time paused.
    #[must_use]
    pub fn start_paused(mut self) -> Self {
        self.start_paused = true;
        self
    }

    /// Set the initial time.
    #[must_use]
    pub fn start_time(mut self, time: Duration) -> Self {
        self.start_time = Some(time);
        self
    }

    /// Enable deterministic task ordering.
    #[must_use]
    pub fn deterministic(mut self) -> Self {
        self.deterministic = true;
        self
    }
}

/// A guard that restores the original time source when dropped.
pub struct TimeGuard {
    _private: (),
}

impl TimeGuard {
    /// Create a new time guard.
    pub(crate) fn new() -> Self {
        Self { _private: () }
    }
}

impl Drop for TimeGuard {
    fn drop(&mut self) {
        // Restore original time source
        // This will be implemented per-runtime
    }
}

#[cfg(feature = "tokio")]
pub mod tokio;

#[cfg(feature = "async-std")]
pub mod async_std;

#[cfg(feature = "smol")]
pub mod smol;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_runtime_config_builder() {
        let config = RuntimeConfig::new()
            .start_paused()
            .start_time(Duration::from_secs(100))
            .deterministic();

        assert!(config.start_paused);
        assert_eq!(config.start_time, Some(Duration::from_secs(100)));
        assert!(config.deterministic);
    }

    #[test]
    fn test_runtime_config_default() {
        let config = RuntimeConfig::default();

        assert!(!config.start_paused);
        assert_eq!(config.start_time, None);
        assert!(!config.deterministic);
    }
}
