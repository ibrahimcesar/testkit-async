#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::needless_pass_by_value)]

//! Tokio runtime integration for testkit-async.
//!
//! This module provides integration with the Tokio async runtime,
//! allowing testkit-async's testing utilities to work seamlessly
//! with Tokio-based applications.
//!
//! # Features
//!
//! - Mock time that works with `tokio::time`
//! - Task spawning compatible with Tokio
//! - Works with `#[tokio::test]` attribute
//!
//! # Example
//!
//! ```rust,ignore
//! use testkit_async::runtime::tokio::TokioRuntime;
//! use std::time::Duration;
//!
//! #[tokio::test]
//! async fn test_with_mock_time() {
//!     let runtime = TokioRuntime::new();
//!     // Use mock time features
//! }
//! ```

use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

use super::{RuntimeConfig, Spawner, TaskJoinHandle, TimeSource};

/// Tokio-based time source using real time.
///
/// This is a thin wrapper around Tokio's time functions.
#[derive(Debug, Clone)]
pub struct TokioTime {
    /// Offset from the start time.
    start: std::time::Instant,
}

impl TokioTime {
    /// Create a new Tokio time source.
    #[must_use]
    pub fn new() -> Self {
        Self {
            start: std::time::Instant::now(),
        }
    }
}

impl Default for TokioTime {
    fn default() -> Self {
        Self::new()
    }
}

impl TimeSource for TokioTime {
    fn now(&self) -> Duration {
        self.start.elapsed()
    }

    fn sleep(&self, duration: Duration) -> Pin<Box<dyn Future<Output = ()> + Send + '_>> {
        Box::pin(::tokio::time::sleep(duration))
    }
}

/// A Tokio-based task spawner.
#[derive(Debug, Clone, Default)]
pub struct TokioSpawner;

impl TokioSpawner {
    /// Create a new Tokio spawner.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

/// Join handle for Tokio tasks.
pub struct TokioJoinHandle<T> {
    inner: ::tokio::task::JoinHandle<T>,
}

impl<T: Send + 'static> TaskJoinHandle for TokioJoinHandle<T> {
    type Output = T;

    fn join(self) -> Pin<Box<dyn Future<Output = Option<Self::Output>> + Send>> {
        Box::pin(async move { self.inner.await.ok() })
    }

    fn abort(&self) {
        self.inner.abort();
    }

    fn is_finished(&self) -> bool {
        self.inner.is_finished()
    }
}

impl Spawner for TokioSpawner {
    type JoinHandle<T: Send + 'static> = TokioJoinHandle<T>;

    fn spawn<F, T>(&self, future: F) -> Self::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        TokioJoinHandle {
            inner: ::tokio::spawn(future),
        }
    }

    fn spawn_named<F, T>(&self, name: &str, future: F) -> Self::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        // Tokio supports named tasks with tracing
        let _ = name;
        self.spawn(future)
    }
}

/// Combined Tokio runtime with time and spawning.
#[derive(Debug, Clone)]
pub struct TokioRuntime {
    time: TokioTime,
    spawner: TokioSpawner,
    config: RuntimeConfig,
}

impl TokioRuntime {
    /// Create a new Tokio runtime wrapper.
    #[must_use]
    pub fn new() -> Self {
        Self::with_config(RuntimeConfig::default())
    }

    /// Create a new Tokio runtime with configuration.
    #[must_use]
    pub fn with_config(config: RuntimeConfig) -> Self {
        Self {
            time: TokioTime::new(),
            spawner: TokioSpawner::new(),
            config,
        }
    }

    /// Get the configuration.
    #[must_use]
    pub fn config(&self) -> &RuntimeConfig {
        &self.config
    }

    /// Run a future to completion on the Tokio runtime.
    ///
    /// This creates a new single-threaded runtime for the test.
    pub fn block_on<F: Future>(&self, future: F) -> F::Output {
        let rt = ::tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .expect("failed to create tokio runtime");
        rt.block_on(future)
    }
}

impl Default for TokioRuntime {
    fn default() -> Self {
        Self::new()
    }
}

impl TimeSource for TokioRuntime {
    fn now(&self) -> Duration {
        self.time.now()
    }

    fn sleep(&self, duration: Duration) -> Pin<Box<dyn Future<Output = ()> + Send + '_>> {
        self.time.sleep(duration)
    }
}

impl Spawner for TokioRuntime {
    type JoinHandle<T: Send + 'static> = TokioJoinHandle<T>;

    fn spawn<F, T>(&self, future: F) -> Self::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        self.spawner.spawn(future)
    }
}

/// Mock time source for Tokio that integrates with MockClock.
///
/// This allows tests to control time while still using Tokio's
/// time-based APIs.
pub struct MockTokioTime {
    /// The current mock time in nanoseconds.
    current_nanos: Arc<AtomicU64>,
    /// Starting time.
    start_nanos: u64,
}

impl MockTokioTime {
    /// Create a new mock Tokio time source.
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

impl Default for MockTokioTime {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for MockTokioTime {
    fn clone(&self) -> Self {
        Self {
            current_nanos: Arc::clone(&self.current_nanos),
            start_nanos: self.start_nanos,
        }
    }
}

impl TimeSource for MockTokioTime {
    fn now(&self) -> Duration {
        self.current()
    }

    fn sleep(&self, duration: Duration) -> Pin<Box<dyn Future<Output = ()> + Send + '_>> {
        // For mock time, we just advance and complete immediately
        // In a real implementation, this would integrate with the executor
        let target = self.now() + duration;
        let current = Arc::clone(&self.current_nanos);
        Box::pin(async move {
            // Set time to target
            current.store(target.as_nanos() as u64, Ordering::SeqCst);
        })
    }
}

/// Run an async test with Tokio and mock time support.
///
/// This function provides a convenient way to run tests that need
/// both Tokio's runtime and mock time control.
///
/// # Example
///
/// ```rust,ignore
/// use testkit_async::runtime::tokio::run_test;
/// use std::time::Duration;
///
/// run_test(|time| async move {
///     time.advance(Duration::from_secs(10));
///     // test code here
/// });
/// ```
pub fn run_test<F, Fut>(test: F)
where
    F: FnOnce(MockTokioTime) -> Fut,
    Fut: Future<Output = ()>,
{
    let rt = ::tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("failed to create tokio runtime");

    let time = MockTokioTime::new();
    rt.block_on(test(time));
}

/// Run an async test with configuration.
pub fn run_test_with_config<F, Fut>(config: RuntimeConfig, test: F)
where
    F: FnOnce(MockTokioTime) -> Fut,
    Fut: Future<Output = ()>,
{
    let rt = ::tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("failed to create tokio runtime");

    let time = if let Some(start) = config.start_time {
        MockTokioTime::with_start_time(start)
    } else {
        MockTokioTime::new()
    };

    rt.block_on(test(time));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokio_time_source() {
        let time = TokioTime::new();
        let now = time.now();
        std::thread::sleep(std::time::Duration::from_millis(10));
        let later = time.now();
        assert!(later > now);
    }

    #[test]
    fn test_mock_tokio_time() {
        let time = MockTokioTime::new();
        assert_eq!(time.current(), Duration::ZERO);

        time.advance(Duration::from_secs(10));
        assert_eq!(time.current(), Duration::from_secs(10));

        time.set(Duration::from_secs(100));
        assert_eq!(time.current(), Duration::from_secs(100));
    }

    #[test]
    fn test_mock_tokio_time_clone_shares_state() {
        let time1 = MockTokioTime::new();
        let time2 = time1.clone();

        time1.advance(Duration::from_secs(5));
        assert_eq!(time2.current(), Duration::from_secs(5));
    }

    #[test]
    fn test_tokio_runtime_config() {
        let runtime = TokioRuntime::with_config(
            RuntimeConfig::new()
                .start_paused()
                .start_time(Duration::from_secs(100)),
        );

        assert!(runtime.config().start_paused);
        assert_eq!(runtime.config().start_time, Some(Duration::from_secs(100)));
    }

    #[tokio::test]
    async fn test_tokio_spawner() {
        let spawner = TokioSpawner::new();

        let handle = spawner.spawn(async { 42 });
        let result = handle.join().await;
        assert_eq!(result, Some(42));
    }

    #[tokio::test]
    async fn test_tokio_spawn_abort() {
        let spawner = TokioSpawner::new();

        let handle = spawner.spawn(async {
            ::tokio::time::sleep(Duration::from_secs(100)).await;
            42
        });

        handle.abort();

        // Give it a moment to abort
        ::tokio::time::sleep(Duration::from_millis(10)).await;
        assert!(handle.is_finished());
    }
}
