//! Future assertion utilities for testing async code.
//!
//! This module provides utilities for testing individual futures:
//!
//! - [`assert_ready!`] - Assert a future is immediately ready
//! - [`assert_pending!`] - Assert a future is not ready
//! - [`poll_once`] - Poll a future once and return the result
//! - [`PollCounter`] - Count how many times a future is polled
//!
//! # Example
//!
//! ```rust,ignore
//! use testkit_async::assertions::{assert_ready, assert_pending, poll_once};
//! use std::task::Poll;
//!
//! // Check immediate readiness
//! let ready_future = async { 42 };
//! assert_ready!(ready_future);
//!
//! // Check pending state
//! let pending_future = futures::future::pending::<i32>();
//! assert_pending!(pending_future);
//! ```

use std::fmt::Debug;
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

/// Poll a future once and return the result.
///
/// This is useful for testing futures without an executor.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::poll_once;
/// use std::task::Poll;
///
/// let ready = async { 42 };
/// let result = poll_once(ready);
/// assert_eq!(result, Poll::Ready(42));
/// ```
pub fn poll_once<F: Future>(future: F) -> Poll<F::Output> {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut pinned = Box::pin(future);
    pinned.as_mut().poll(&mut cx)
}

/// Assert that a future is immediately ready.
///
/// # Panics
///
/// Panics if the future returns `Poll::Pending`.
///
/// # Example
///
/// ```rust
/// use testkit_async::assert_ready;
///
/// let ready = async { 42 };
/// let value = assert_ready!(ready);
/// assert_eq!(value, 42);
/// ```
#[macro_export]
macro_rules! assert_ready {
    ($future:expr) => {{
        match $crate::assertions::poll_once($future) {
            ::std::task::Poll::Ready(value) => value,
            ::std::task::Poll::Pending => {
                panic!("assertion failed: expected future to be Ready, but it was Pending");
            }
        }
    }};
    ($future:expr, $($arg:tt)+) => {{
        match $crate::assertions::poll_once($future) {
            ::std::task::Poll::Ready(value) => value,
            ::std::task::Poll::Pending => {
                panic!("assertion failed: expected future to be Ready, but it was Pending: {}", format_args!($($arg)+));
            }
        }
    }};
}

/// Assert that a future is pending (not ready).
///
/// # Panics
///
/// Panics if the future returns `Poll::Ready`.
///
/// # Example
///
/// ```rust
/// use testkit_async::assert_pending;
///
/// let pending = futures::future::pending::<i32>();
/// assert_pending!(pending);
/// ```
#[macro_export]
macro_rules! assert_pending {
    ($future:expr) => {{
        match $crate::assertions::poll_once($future) {
            ::std::task::Poll::Pending => {}
            ::std::task::Poll::Ready(value) => {
                panic!(
                    "assertion failed: expected future to be Pending, but it was Ready({:?})",
                    value
                );
            }
        }
    }};
    ($future:expr, $($arg:tt)+) => {{
        match $crate::assertions::poll_once($future) {
            ::std::task::Poll::Pending => {}
            ::std::task::Poll::Ready(value) => {
                panic!(
                    "assertion failed: expected future to be Pending, but it was Ready({:?}): {}",
                    value,
                    format_args!($($arg)+)
                );
            }
        }
    }};
}

/// Assert that a future resolves to a specific value.
///
/// Awaits the future and compares the result.
///
/// # Panics
///
/// Panics if the future result doesn't match expected.
///
/// # Example
///
/// ```rust,ignore
/// use testkit_async::assert_resolves_to;
///
/// async fn get_value() -> i32 { 42 }
///
/// assert_resolves_to!(42, get_value()).await;
/// ```
#[macro_export]
macro_rules! assert_resolves_to {
    ($expected:expr, $future:expr) => {{
        let result = $future.await;
        assert_eq!(
            result, $expected,
            "assertion failed: future resolved to {:?}, expected {:?}",
            result, $expected
        );
        result
    }};
}

/// Assert that a future resolves to `Ok`.
///
/// # Panics
///
/// Panics if the future resolves to `Err`.
///
/// # Example
///
/// ```rust,ignore
/// use testkit_async::assert_resolves_ok;
///
/// async fn get_result() -> Result<i32, &'static str> { Ok(42) }
///
/// let value = assert_resolves_ok!(get_result()).await;
/// assert_eq!(value, 42);
/// ```
#[macro_export]
macro_rules! assert_resolves_ok {
    ($future:expr) => {{
        let future = $future;
        async move {
            match future.await {
                Ok(value) => value,
                Err(err) => panic!(
                    "assertion failed: expected Ok, got Err({:?})",
                    err
                ),
            }
        }
    }};
}

/// Assert that a future resolves to `Err`.
///
/// # Panics
///
/// Panics if the future resolves to `Ok`.
///
/// # Example
///
/// ```rust,ignore
/// use testkit_async::assert_resolves_err;
///
/// async fn get_error() -> Result<i32, &'static str> { Err("oops") }
///
/// let err = assert_resolves_err!(get_error()).await;
/// assert_eq!(err, "oops");
/// ```
#[macro_export]
macro_rules! assert_resolves_err {
    ($future:expr) => {{
        let future = $future;
        async move {
            match future.await {
                Err(err) => err,
                Ok(value) => panic!(
                    "assertion failed: expected Err, got Ok({:?})",
                    value
                ),
            }
        }
    }};
}

/// A wrapper that counts how many times a future is polled.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::PollCounter;
/// use std::future::ready;
///
/// let (future, counter) = PollCounter::wrap(ready(42));
///
/// // Poll the future
/// let result = futures::executor::block_on(future);
///
/// assert_eq!(result, 42);
/// assert!(counter.count() >= 1);
/// ```
pub struct PollCounter<F> {
    inner: F,
    count: Arc<AtomicUsize>,
}

impl<F: Future> PollCounter<F> {
    /// Wrap a future and create a counter handle.
    ///
    /// Returns the wrapped future and a handle to read the poll count.
    pub fn wrap(future: F) -> (Self, PollCountHandle) {
        let count = Arc::new(AtomicUsize::new(0));
        (
            Self {
                inner: future,
                count: Arc::clone(&count),
            },
            PollCountHandle { count },
        )
    }
}

impl<F: Future + Unpin> Future for PollCounter<F> {
    type Output = F::Output;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.count.fetch_add(1, Ordering::SeqCst);
        Pin::new(&mut self.inner).poll(cx)
    }
}

/// Handle to read the poll count from a [`PollCounter`].
#[derive(Clone)]
pub struct PollCountHandle {
    count: Arc<AtomicUsize>,
}

impl PollCountHandle {
    /// Get the current poll count.
    #[must_use]
    pub fn count(&self) -> usize {
        self.count.load(Ordering::SeqCst)
    }

    /// Reset the poll count to zero.
    pub fn reset(&self) {
        self.count.store(0, Ordering::SeqCst);
    }
}

impl Debug for PollCountHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PollCountHandle")
            .field("count", &self.count())
            .finish()
    }
}

/// Create a future that completes after being polled N times.
///
/// Useful for testing poll behavior.
///
/// # Example
///
/// ```rust
/// use testkit_async::assertions::ready_after_polls;
///
/// let future = ready_after_polls(3, "done");
///
/// // Will be pending for first 2 polls, then ready on the 3rd
/// ```
pub fn ready_after_polls<T>(polls_until_ready: usize, value: T) -> ReadyAfterPolls<T> {
    ReadyAfterPolls {
        remaining: polls_until_ready,
        value: Some(value),
    }
}

/// A future that completes after a certain number of polls.
pub struct ReadyAfterPolls<T> {
    remaining: usize,
    value: Option<T>,
}

impl<T: Unpin> Future for ReadyAfterPolls<T> {
    type Output = T;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.remaining == 0 {
            Poll::Ready(self.value.take().expect("polled after completion"))
        } else {
            self.remaining -= 1;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

/// Result of polling a future.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FuturePollResult<T> {
    /// Future is ready with a value.
    Ready(T),
    /// Future is still pending.
    Pending,
}

impl<T> FuturePollResult<T> {
    /// Returns `true` if the result is `Ready`.
    #[must_use]
    pub fn is_ready(&self) -> bool {
        matches!(self, Self::Ready(_))
    }

    /// Returns `true` if the result is `Pending`.
    #[must_use]
    pub fn is_pending(&self) -> bool {
        matches!(self, Self::Pending)
    }

    /// Unwrap the ready value, panicking if pending.
    ///
    /// # Panics
    ///
    /// Panics if the result is `Pending`.
    #[must_use]
    pub fn unwrap(self) -> T {
        match self {
            Self::Ready(v) => v,
            Self::Pending => panic!("called `unwrap()` on a `Pending` value"),
        }
    }

    /// Convert to an Option.
    #[must_use]
    pub fn ready(self) -> Option<T> {
        match self {
            Self::Ready(v) => Some(v),
            Self::Pending => None,
        }
    }
}

impl<T> From<Poll<T>> for FuturePollResult<T> {
    fn from(poll: Poll<T>) -> Self {
        match poll {
            Poll::Ready(v) => Self::Ready(v),
            Poll::Pending => Self::Pending,
        }
    }
}

// Create a no-op waker for polling futures
fn noop_waker() -> Waker {
    const VTABLE: RawWakerVTable = RawWakerVTable::new(
        |_| RawWaker::new(std::ptr::null(), &VTABLE),
        |_| {},
        |_| {},
        |_| {},
    );

    unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::future::ready;

    #[test]
    fn test_poll_once_ready() {
        let result = poll_once(ready(42));
        assert_eq!(result, Poll::Ready(42));
    }

    #[test]
    fn test_poll_once_pending() {
        let result = poll_once(futures::future::pending::<i32>());
        assert_eq!(result, Poll::Pending);
    }

    #[test]
    fn test_assert_ready_success() {
        let value = assert_ready!(ready(42));
        assert_eq!(value, 42);
    }

    #[test]
    #[should_panic(expected = "expected future to be Ready")]
    fn test_assert_ready_failure() {
        assert_ready!(futures::future::pending::<i32>());
    }

    #[test]
    fn test_assert_pending_success() {
        assert_pending!(futures::future::pending::<i32>());
    }

    #[test]
    #[should_panic(expected = "expected future to be Pending")]
    fn test_assert_pending_failure() {
        assert_pending!(ready(42));
    }

    #[test]
    fn test_poll_counter() {
        let (future, counter) = PollCounter::wrap(ready_after_polls(3, "done"));

        assert_eq!(counter.count(), 0);

        let result = futures::executor::block_on(future);

        assert_eq!(result, "done");
        // The future is polled 3 times as Pending (remaining goes 3->2->1->0),
        // then once more when ready. The executor may also poll an extra time.
        assert!(counter.count() >= 3);
    }

    #[test]
    fn test_poll_counter_reset() {
        let (_future, counter) = PollCounter::wrap(ready(42));
        counter.reset();
        assert_eq!(counter.count(), 0);
    }

    #[test]
    fn test_ready_after_polls() {
        let future = ready_after_polls(2, "value");

        let waker = noop_waker();
        let mut cx = Context::from_waker(&waker);
        let mut pinned = Box::pin(future);

        // First poll - pending (remaining goes from 2 to 1)
        assert!(pinned.as_mut().poll(&mut cx).is_pending());

        // Second poll - pending (remaining goes from 1 to 0)
        assert!(pinned.as_mut().poll(&mut cx).is_pending());

        // Third poll - ready (remaining is 0)
        match pinned.as_mut().poll(&mut cx) {
            Poll::Ready(v) => assert_eq!(v, "value"),
            Poll::Pending => panic!("expected ready"),
        }
    }

    #[test]
    fn test_ready_after_zero_polls() {
        let future = ready_after_polls(0, "immediate");
        let result = poll_once(future);
        assert_eq!(result, Poll::Ready("immediate"));
    }

    #[test]
    fn test_future_poll_result_is_ready() {
        let ready: FuturePollResult<i32> = FuturePollResult::Ready(42);
        let pending: FuturePollResult<i32> = FuturePollResult::Pending;

        assert!(ready.is_ready());
        assert!(!ready.is_pending());
        assert!(!pending.is_ready());
        assert!(pending.is_pending());
    }

    #[test]
    fn test_future_poll_result_unwrap() {
        let ready: FuturePollResult<i32> = FuturePollResult::Ready(42);
        assert_eq!(ready.unwrap(), 42);
    }

    #[test]
    #[should_panic(expected = "called `unwrap()` on a `Pending` value")]
    fn test_future_poll_result_unwrap_panics() {
        let pending: FuturePollResult<i32> = FuturePollResult::Pending;
        pending.unwrap();
    }

    #[test]
    fn test_future_poll_result_ready() {
        let ready: FuturePollResult<i32> = FuturePollResult::Ready(42);
        let pending: FuturePollResult<i32> = FuturePollResult::Pending;

        assert_eq!(ready.ready(), Some(42));
        assert_eq!(pending.ready(), None);
    }

    #[test]
    fn test_future_poll_result_from_poll() {
        let ready: FuturePollResult<i32> = Poll::Ready(42).into();
        let pending: FuturePollResult<i32> = Poll::<i32>::Pending.into();

        assert_eq!(ready, FuturePollResult::Ready(42));
        assert_eq!(pending, FuturePollResult::Pending);
    }

    #[tokio::test]
    async fn test_assert_resolves_to() {
        async fn get_value() -> i32 {
            42
        }
        assert_resolves_to!(42, get_value());
    }

    #[tokio::test]
    async fn test_assert_resolves_ok() {
        async fn get_result() -> Result<i32, &'static str> {
            Ok(42)
        }
        let value = assert_resolves_ok!(get_result()).await;
        assert_eq!(value, 42);
    }

    #[tokio::test]
    async fn test_assert_resolves_err() {
        async fn get_error() -> Result<i32, &'static str> {
            Err("oops")
        }
        let err = assert_resolves_err!(get_error()).await;
        assert_eq!(err, "oops");
    }
}
