#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::needless_pass_by_value)]

//! async-std runtime integration for testkit-async.
//!
//! This module provides integration with the async-std async runtime,
//! allowing testkit-async's testing utilities to work seamlessly
//! with async-std-based applications.
//!
//! # Features
//!
//! - Mock time that works with `async_std::task`
//! - Task spawning compatible with async-std
//! - Works with `#[async_std::test]` attribute
//!
//! # Example
//!
//! ```rust,ignore
//! use testkit_async::runtime::async_std::AsyncStdRuntime;
//! use std::time::Duration;
//!
//! #[async_std::test]
//! async fn test_with_mock_time() {
//!     let runtime = AsyncStdRuntime::new();
//!     // Use mock time features
//! }
//! ```

use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

use super::{RuntimeConfig, Spawner, TaskJoinHandle, TimeSource};

/// async-std-based time source using real time.
///
/// This is a thin wrapper around async-std's time functions.
#[derive(Debug, Clone)]
pub struct AsyncStdTime {
    /// Offset from the start time.
    start: std::time::Instant,
}

impl AsyncStdTime {
    /// Create a new async-std time source.
    #[must_use]
    pub fn new() -> Self {
        Self {
            start: std::time::Instant::now(),
        }
    }
}

impl Default for AsyncStdTime {
    fn default() -> Self {
        Self::new()
    }
}

impl TimeSource for AsyncStdTime {
    fn now(&self) -> Duration {
        self.start.elapsed()
    }

    fn sleep(&self, duration: Duration) -> Pin<Box<dyn Future<Output = ()> + Send + '_>> {
        Box::pin(::async_std::task::sleep(duration))
    }
}

/// An async-std-based task spawner.
#[derive(Debug, Clone, Default)]
pub struct AsyncStdSpawner;

impl AsyncStdSpawner {
    /// Create a new async-std spawner.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

/// Join handle for async-std tasks.
pub struct AsyncStdJoinHandle<T> {
    inner: ::async_std::task::JoinHandle<T>,
}

impl<T: Send + 'static> TaskJoinHandle for AsyncStdJoinHandle<T> {
    type Output = T;

    fn join(self) -> Pin<Box<dyn Future<Output = Option<Self::Output>> + Send>> {
        Box::pin(async move { Some(self.inner.await) })
    }

    fn abort(&self) {
        // async-std doesn't have built-in abort support
        // This is a limitation of async-std's JoinHandle
    }

    fn is_finished(&self) -> bool {
        // async-std doesn't have is_finished support
        // This is a limitation of async-std's JoinHandle
        false
    }
}

impl Spawner for AsyncStdSpawner {
    type JoinHandle<T: Send + 'static> = AsyncStdJoinHandle<T>;

    fn spawn<F, T>(&self, future: F) -> Self::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        AsyncStdJoinHandle {
            inner: ::async_std::task::spawn(future),
        }
    }

    fn spawn_named<F, T>(&self, name: &str, future: F) -> Self::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        // async-std supports named tasks via Builder
        let _ = name;
        self.spawn(future)
    }
}

/// Combined async-std runtime with time and spawning.
#[derive(Debug, Clone)]
pub struct AsyncStdRuntime {
    time: AsyncStdTime,
    spawner: AsyncStdSpawner,
    config: RuntimeConfig,
}

impl AsyncStdRuntime {
    /// Create a new async-std runtime wrapper.
    #[must_use]
    pub fn new() -> Self {
        Self::with_config(RuntimeConfig::default())
    }

    /// Create a new async-std runtime with configuration.
    #[must_use]
    pub fn with_config(config: RuntimeConfig) -> Self {
        Self {
            time: AsyncStdTime::new(),
            spawner: AsyncStdSpawner::new(),
            config,
        }
    }

    /// Get the configuration.
    #[must_use]
    pub fn config(&self) -> &RuntimeConfig {
        &self.config
    }

    /// Run a future to completion on async-std.
    ///
    /// This blocks the current thread until the future completes.
    pub fn block_on<F: Future>(&self, future: F) -> F::Output {
        ::async_std::task::block_on(future)
    }
}

impl Default for AsyncStdRuntime {
    fn default() -> Self {
        Self::new()
    }
}

impl TimeSource for AsyncStdRuntime {
    fn now(&self) -> Duration {
        self.time.now()
    }

    fn sleep(&self, duration: Duration) -> Pin<Box<dyn Future<Output = ()> + Send + '_>> {
        self.time.sleep(duration)
    }
}

impl Spawner for AsyncStdRuntime {
    type JoinHandle<T: Send + 'static> = AsyncStdJoinHandle<T>;

    fn spawn<F, T>(&self, future: F) -> Self::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        self.spawner.spawn(future)
    }
}

/// Mock time source for async-std that integrates with MockClock.
///
/// This allows tests to control time while still using async-std's
/// time-based APIs.
pub struct MockAsyncStdTime {
    /// The current mock time in nanoseconds.
    current_nanos: Arc<AtomicU64>,
    /// Starting time.
    start_nanos: u64,
}

impl MockAsyncStdTime {
    /// Create a new mock async-std time source.
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

impl Default for MockAsyncStdTime {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for MockAsyncStdTime {
    fn clone(&self) -> Self {
        Self {
            current_nanos: Arc::clone(&self.current_nanos),
            start_nanos: self.start_nanos,
        }
    }
}

impl TimeSource for MockAsyncStdTime {
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

/// Run an async test with async-std and mock time support.
///
/// This function provides a convenient way to run tests that need
/// both async-std's runtime and mock time control.
///
/// # Example
///
/// ```rust,ignore
/// use testkit_async::runtime::async_std::run_test;
/// use std::time::Duration;
///
/// run_test(|time| async move {
///     time.advance(Duration::from_secs(10));
///     // test code here
/// });
/// ```
pub fn run_test<F, Fut>(test: F)
where
    F: FnOnce(MockAsyncStdTime) -> Fut,
    Fut: Future<Output = ()>,
{
    let time = MockAsyncStdTime::new();
    ::async_std::task::block_on(test(time));
}

/// Run an async test with configuration.
pub fn run_test_with_config<F, Fut>(config: RuntimeConfig, test: F)
where
    F: FnOnce(MockAsyncStdTime) -> Fut,
    Fut: Future<Output = ()>,
{
    let time = if let Some(start) = config.start_time {
        MockAsyncStdTime::with_start_time(start)
    } else {
        MockAsyncStdTime::new()
    };

    ::async_std::task::block_on(test(time));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_async_std_time_source() {
        let time = AsyncStdTime::new();
        let now = time.now();
        std::thread::sleep(std::time::Duration::from_millis(10));
        let later = time.now();
        assert!(later > now);
    }

    #[test]
    fn test_mock_async_std_time() {
        let time = MockAsyncStdTime::new();
        assert_eq!(time.current(), Duration::ZERO);

        time.advance(Duration::from_secs(10));
        assert_eq!(time.current(), Duration::from_secs(10));

        time.set(Duration::from_secs(100));
        assert_eq!(time.current(), Duration::from_secs(100));
    }

    #[test]
    fn test_mock_async_std_time_clone_shares_state() {
        let time1 = MockAsyncStdTime::new();
        let time2 = time1.clone();

        time1.advance(Duration::from_secs(5));
        assert_eq!(time2.current(), Duration::from_secs(5));
    }

    #[test]
    fn test_async_std_runtime_config() {
        let runtime = AsyncStdRuntime::with_config(
            RuntimeConfig::new()
                .start_paused()
                .start_time(Duration::from_secs(100)),
        );

        assert!(runtime.config().start_paused);
        assert_eq!(runtime.config().start_time, Some(Duration::from_secs(100)));
    }
}
