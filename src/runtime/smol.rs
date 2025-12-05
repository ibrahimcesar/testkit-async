#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::needless_pass_by_value)]

//! smol runtime integration for testkit-async.
//!
//! This module provides integration with the smol async runtime,
//! allowing testkit-async's testing utilities to work seamlessly
//! with smol-based applications.
//!
//! # Features
//!
//! - Mock time that works with `smol::Timer`
//! - Task spawning compatible with smol
//! - Lightweight executor integration
//!
//! # Example
//!
//! ```rust,ignore
//! use testkit_async::runtime::smol::SmolRuntime;
//! use std::time::Duration;
//!
//! fn main() {
//!     smol::block_on(async {
//!         let runtime = SmolRuntime::new();
//!         // Use mock time features
//!     });
//! }
//! ```

use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

use super::{RuntimeConfig, Spawner, TaskJoinHandle, TimeSource};

/// smol-based time source using real time.
///
/// This is a thin wrapper around smol's time functions.
#[derive(Debug, Clone)]
pub struct SmolTime {
    /// Offset from the start time.
    start: std::time::Instant,
}

impl SmolTime {
    /// Create a new smol time source.
    #[must_use]
    pub fn new() -> Self {
        Self {
            start: std::time::Instant::now(),
        }
    }
}

impl Default for SmolTime {
    fn default() -> Self {
        Self::new()
    }
}

impl TimeSource for SmolTime {
    fn now(&self) -> Duration {
        self.start.elapsed()
    }

    fn sleep(&self, duration: Duration) -> Pin<Box<dyn Future<Output = ()> + Send + '_>> {
        Box::pin(async move {
            ::smol::Timer::after(duration).await;
        })
    }
}

/// A smol-based task spawner.
#[derive(Debug, Clone, Default)]
pub struct SmolSpawner;

impl SmolSpawner {
    /// Create a new smol spawner.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

/// Join handle for smol tasks.
pub struct SmolJoinHandle<T> {
    inner: ::smol::Task<T>,
}

impl<T: Send + 'static> TaskJoinHandle for SmolJoinHandle<T> {
    type Output = T;

    fn join(self) -> Pin<Box<dyn Future<Output = Option<Self::Output>> + Send>> {
        Box::pin(async move { Some(self.inner.await) })
    }

    fn abort(&self) {
        // smol Task has a cancel() method but it consumes self
        // For this interface, we can't implement abort without consuming
    }

    fn is_finished(&self) -> bool {
        // smol doesn't expose is_finished on Task
        false
    }
}

impl Spawner for SmolSpawner {
    type JoinHandle<T: Send + 'static> = SmolJoinHandle<T>;

    fn spawn<F, T>(&self, future: F) -> Self::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        SmolJoinHandle {
            inner: ::smol::spawn(future),
        }
    }

    fn spawn_named<F, T>(&self, name: &str, future: F) -> Self::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        // smol doesn't have named task support
        let _ = name;
        self.spawn(future)
    }
}

/// Combined smol runtime with time and spawning.
#[derive(Debug, Clone)]
pub struct SmolRuntime {
    time: SmolTime,
    spawner: SmolSpawner,
    config: RuntimeConfig,
}

impl SmolRuntime {
    /// Create a new smol runtime wrapper.
    #[must_use]
    pub fn new() -> Self {
        Self::with_config(RuntimeConfig::default())
    }

    /// Create a new smol runtime with configuration.
    #[must_use]
    pub fn with_config(config: RuntimeConfig) -> Self {
        Self {
            time: SmolTime::new(),
            spawner: SmolSpawner::new(),
            config,
        }
    }

    /// Get the configuration.
    #[must_use]
    pub fn config(&self) -> &RuntimeConfig {
        &self.config
    }

    /// Run a future to completion on smol.
    ///
    /// This blocks the current thread until the future completes.
    pub fn block_on<F: Future>(&self, future: F) -> F::Output {
        ::smol::block_on(future)
    }
}

impl Default for SmolRuntime {
    fn default() -> Self {
        Self::new()
    }
}

impl TimeSource for SmolRuntime {
    fn now(&self) -> Duration {
        self.time.now()
    }

    fn sleep(&self, duration: Duration) -> Pin<Box<dyn Future<Output = ()> + Send + '_>> {
        self.time.sleep(duration)
    }
}

impl Spawner for SmolRuntime {
    type JoinHandle<T: Send + 'static> = SmolJoinHandle<T>;

    fn spawn<F, T>(&self, future: F) -> Self::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        self.spawner.spawn(future)
    }
}

/// Mock time source for smol that integrates with MockClock.
///
/// This allows tests to control time while still using smol's
/// time-based APIs.
pub struct MockSmolTime {
    /// The current mock time in nanoseconds.
    current_nanos: Arc<AtomicU64>,
    /// Starting time.
    start_nanos: u64,
}

impl MockSmolTime {
    /// Create a new mock smol time source.
    #[must_use]
    pub fn new() -> Self {
        Self {
            current_nanos: Arc::new(AtomicU64::new(0)),
            start_nanos: 0,
        }
    }

    /// Create with a specific starting time.
    #[must_use]
    pub fn with_start_time(start: Duration) -> Self {
        let nanos = start.as_nanos() as u64;
        Self {
            current_nanos: Arc::new(AtomicU64::new(nanos)),
            start_nanos: nanos,
        }
    }

    /// Advance time by the given duration.
    pub fn advance(&self, duration: Duration) {
        let nanos = duration.as_nanos() as u64;
        self.current_nanos.fetch_add(nanos, Ordering::SeqCst);
    }

    /// Set time to a specific point.
    pub fn set(&self, time: Duration) {
        let nanos = time.as_nanos() as u64;
        self.current_nanos.store(nanos, Ordering::SeqCst);
    }

    /// Get the current mock time.
    #[must_use]
    pub fn current(&self) -> Duration {
        Duration::from_nanos(self.current_nanos.load(Ordering::SeqCst))
    }

    /// Get elapsed time since start.
    #[must_use]
    pub fn elapsed(&self) -> Duration {
        let current = self.current_nanos.load(Ordering::SeqCst);
        Duration::from_nanos(current.saturating_sub(self.start_nanos))
    }
}

impl Default for MockSmolTime {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for MockSmolTime {
    fn clone(&self) -> Self {
        Self {
            current_nanos: Arc::clone(&self.current_nanos),
            start_nanos: self.start_nanos,
        }
    }
}

impl TimeSource for MockSmolTime {
    fn now(&self) -> Duration {
        self.current()
    }

    fn sleep(&self, duration: Duration) -> Pin<Box<dyn Future<Output = ()> + Send + '_>> {
        // For mock time, we just advance and complete immediately
        let target = self.now() + duration;
        let current = Arc::clone(&self.current_nanos);
        Box::pin(async move {
            current.store(target.as_nanos() as u64, Ordering::SeqCst);
        })
    }
}

/// Run an async test with smol and mock time support.
///
/// This function provides a convenient way to run tests that need
/// both smol's runtime and mock time control.
///
/// # Example
///
/// ```rust,ignore
/// use testkit_async::runtime::smol::run_test;
/// use std::time::Duration;
///
/// run_test(|time| async move {
///     time.advance(Duration::from_secs(10));
///     // test code here
/// });
/// ```
pub fn run_test<F, Fut>(test: F)
where
    F: FnOnce(MockSmolTime) -> Fut,
    Fut: Future<Output = ()>,
{
    let time = MockSmolTime::new();
    ::smol::block_on(test(time));
}

/// Run an async test with configuration.
pub fn run_test_with_config<F, Fut>(config: RuntimeConfig, test: F)
where
    F: FnOnce(MockSmolTime) -> Fut,
    Fut: Future<Output = ()>,
{
    let time = if let Some(start) = config.start_time {
        MockSmolTime::with_start_time(start)
    } else {
        MockSmolTime::new()
    };

    ::smol::block_on(test(time));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_smol_time_source() {
        let time = SmolTime::new();
        let now = time.now();
        std::thread::sleep(std::time::Duration::from_millis(10));
        let later = time.now();
        assert!(later > now);
    }

    #[test]
    fn test_mock_smol_time() {
        let time = MockSmolTime::new();
        assert_eq!(time.current(), Duration::ZERO);

        time.advance(Duration::from_secs(10));
        assert_eq!(time.current(), Duration::from_secs(10));

        time.set(Duration::from_secs(100));
        assert_eq!(time.current(), Duration::from_secs(100));
    }

    #[test]
    fn test_mock_smol_time_clone_shares_state() {
        let time1 = MockSmolTime::new();
        let time2 = time1.clone();

        time1.advance(Duration::from_secs(5));
        assert_eq!(time2.current(), Duration::from_secs(5));
    }

    #[test]
    fn test_smol_runtime_config() {
        let runtime = SmolRuntime::with_config(
            RuntimeConfig::new()
                .start_paused()
                .start_time(Duration::from_secs(100)),
        );

        assert!(runtime.config().start_paused);
        assert_eq!(runtime.config().start_time, Some(Duration::from_secs(100)));
    }
}
