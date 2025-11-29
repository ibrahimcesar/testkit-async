//! `MockClock` implementation for virtual time control.

use parking_lot::Mutex;
use std::sync::Arc;
use std::time::Duration;

use super::sleep::{MockDelay, MockSleep, SleepState};

/// A mock clock that provides virtual time control for async tests.
///
/// `MockClock` allows you to control the passage of time in your tests,
/// making it possible to test time-dependent code without waiting for
/// real time to pass.
///
/// # Thread Safety
///
/// `MockClock` is thread-safe and can be cloned and shared across threads.
/// All clones share the same underlying time state.
///
/// # Example
///
/// ```rust
/// use testkit_async::clock::MockClock;
/// use std::time::Duration;
///
/// // Create a new clock starting at time zero
/// let clock = MockClock::new();
/// assert_eq!(clock.now(), Duration::ZERO);
///
/// // Advance time by 10 seconds
/// clock.advance(Duration::from_secs(10));
/// assert_eq!(clock.now(), Duration::from_secs(10));
///
/// // Clone shares the same time
/// let clock2 = clock.clone();
/// assert_eq!(clock2.now(), Duration::from_secs(10));
///
/// // Advancing one advances both
/// clock2.advance(Duration::from_secs(5));
/// assert_eq!(clock.now(), Duration::from_secs(15));
/// ```
#[derive(Debug, Clone)]
pub struct MockClock {
    pub(crate) inner: Arc<ClockInner>,
}

#[derive(Debug)]
pub(crate) struct ClockInner {
    /// Current virtual time
    state: Mutex<ClockState>,
    /// Pending sleeps
    pub(crate) sleeps: Mutex<SleepState>,
}

#[derive(Debug)]
struct ClockState {
    /// Current time as duration since clock creation
    current_time: Duration,
    /// Whether the clock is paused
    paused: bool,
}

impl Default for MockClock {
    fn default() -> Self {
        Self::new()
    }
}

impl MockClock {
    /// Creates a new `MockClock` starting at time zero.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::MockClock;
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::new();
    /// assert_eq!(clock.now(), Duration::ZERO);
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self::with_start_time(Duration::ZERO)
    }

    /// Creates a new `MockClock` starting at the specified time.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::MockClock;
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::with_start_time(Duration::from_secs(100));
    /// assert_eq!(clock.now(), Duration::from_secs(100));
    /// ```
    #[must_use]
    pub fn with_start_time(start: Duration) -> Self {
        Self {
            inner: Arc::new(ClockInner {
                state: Mutex::new(ClockState {
                    current_time: start,
                    paused: false,
                }),
                sleeps: Mutex::new(SleepState::new()),
            }),
        }
    }

    /// Returns the current virtual time.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::MockClock;
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::new();
    /// assert_eq!(clock.now(), Duration::ZERO);
    ///
    /// clock.advance(Duration::from_secs(5));
    /// assert_eq!(clock.now(), Duration::from_secs(5));
    /// ```
    #[must_use]
    pub fn now(&self) -> Duration {
        self.inner.state.lock().current_time
    }

    /// Advances the clock by the specified duration.
    ///
    /// This is the primary method for moving time forward in tests.
    /// Any pending sleeps or delays that should complete during this
    /// time advancement will be triggered.
    ///
    /// # Panics
    ///
    /// Panics if the clock is paused.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::MockClock;
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::new();
    /// clock.advance(Duration::from_secs(10));
    /// assert_eq!(clock.now(), Duration::from_secs(10));
    ///
    /// clock.advance(Duration::from_millis(500));
    /// assert_eq!(clock.now(), Duration::from_millis(10_500));
    /// ```
    pub fn advance(&self, duration: Duration) {
        let new_time = {
            let mut state = self.inner.state.lock();
            assert!(!state.paused, "Cannot advance time while clock is paused");
            state.current_time += duration;
            state.current_time
        };
        // Wake any sleeps that have expired
        self.inner.sleeps.lock().wake_expired(new_time);
    }

    /// Sets the clock to an absolute time.
    ///
    /// Unlike `advance`, this allows setting time to any value,
    /// including values less than the current time.
    ///
    /// # Warning
    ///
    /// Setting time backwards may cause unexpected behavior with pending
    /// sleeps or delays. Use with caution.
    ///
    /// # Panics
    ///
    /// Panics if the clock is paused.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::MockClock;
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::new();
    /// clock.set(Duration::from_secs(100));
    /// assert_eq!(clock.now(), Duration::from_secs(100));
    /// ```
    pub fn set(&self, time: Duration) {
        let mut state = self.inner.state.lock();
        assert!(!state.paused, "Cannot set time while clock is paused");
        state.current_time = time;
    }

    /// Advances the clock to a specific time.
    ///
    /// This method only moves time forward - if the specified time
    /// is less than or equal to the current time, this is a no-op.
    ///
    /// # Panics
    ///
    /// Panics if the clock is paused.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::MockClock;
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::new();
    /// clock.advance_to(Duration::from_secs(10));
    /// assert_eq!(clock.now(), Duration::from_secs(10));
    ///
    /// // Trying to go backwards is a no-op
    /// clock.advance_to(Duration::from_secs(5));
    /// assert_eq!(clock.now(), Duration::from_secs(10));
    /// ```
    pub fn advance_to(&self, time: Duration) {
        let mut state = self.inner.state.lock();
        assert!(!state.paused, "Cannot advance time while clock is paused");
        if time > state.current_time {
            state.current_time = time;
        }
    }

    /// Returns the elapsed time since the clock was created.
    ///
    /// This is equivalent to `now()` when the clock starts at zero.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::MockClock;
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::with_start_time(Duration::from_secs(100));
    /// assert_eq!(clock.elapsed(), Duration::from_secs(100));
    ///
    /// clock.advance(Duration::from_secs(50));
    /// assert_eq!(clock.elapsed(), Duration::from_secs(150));
    /// ```
    #[must_use]
    pub fn elapsed(&self) -> Duration {
        self.now()
    }

    /// Pauses the clock, preventing time from advancing.
    ///
    /// While paused, calls to `advance`, `set`, or `advance_to` will panic.
    /// Use `resume` to unpause the clock.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::MockClock;
    ///
    /// let clock = MockClock::new();
    /// assert!(!clock.is_paused());
    ///
    /// clock.pause();
    /// assert!(clock.is_paused());
    /// ```
    pub fn pause(&self) {
        self.inner.state.lock().paused = true;
    }

    /// Resumes a paused clock.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::MockClock;
    ///
    /// let clock = MockClock::new();
    /// clock.pause();
    /// assert!(clock.is_paused());
    ///
    /// clock.resume();
    /// assert!(!clock.is_paused());
    /// ```
    pub fn resume(&self) {
        self.inner.state.lock().paused = false;
    }

    /// Returns whether the clock is currently paused.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::MockClock;
    ///
    /// let clock = MockClock::new();
    /// assert!(!clock.is_paused());
    ///
    /// clock.pause();
    /// assert!(clock.is_paused());
    /// ```
    #[must_use]
    pub fn is_paused(&self) -> bool {
        self.inner.state.lock().paused
    }

    /// Creates a sleep future that completes when virtual time advances past its deadline.
    ///
    /// This is the primary way to sleep in tests using `MockClock`. The sleep completes
    /// instantly when you call `advance()` past its deadline.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use testkit_async::clock::MockClock;
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::new();
    ///
    /// // Spawn a task that sleeps
    /// let clock2 = clock.clone();
    /// let handle = tokio::spawn(async move {
    ///     clock2.sleep(Duration::from_secs(10)).await;
    ///     println!("Woke up!");
    /// });
    ///
    /// // Advance time - the sleep completes instantly!
    /// clock.advance(Duration::from_secs(10));
    /// ```
    #[must_use]
    pub fn sleep(&self, duration: Duration) -> MockSleep {
        MockSleep::new(self.clone(), duration)
    }

    /// Creates a delay future that completes after the specified virtual duration.
    ///
    /// This is similar to `sleep` but returns a `MockDelay` which can provide
    /// additional information about the delay state.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::MockClock;
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::new();
    /// let delay = clock.delay(Duration::from_secs(10));
    ///
    /// assert_eq!(delay.deadline(), Duration::from_secs(10));
    /// assert!(!delay.is_elapsed());
    ///
    /// clock.advance(Duration::from_secs(10));
    /// assert!(delay.is_elapsed());
    /// ```
    #[must_use]
    pub fn delay(&self, duration: Duration) -> MockDelay {
        MockDelay::new(self.clone(), duration)
    }

    /// Returns the number of pending sleeps waiting to complete.
    ///
    /// This is useful for debugging and verifying test behavior.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::MockClock;
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::new();
    /// assert_eq!(clock.pending_count(), 0);
    ///
    /// let _sleep1 = clock.sleep(Duration::from_secs(10));
    /// let _sleep2 = clock.sleep(Duration::from_secs(20));
    ///
    /// // Sleeps are registered when first polled, not when created
    /// // so pending_count is still 0 until the futures are polled
    /// ```
    #[must_use]
    pub fn pending_count(&self) -> usize {
        self.inner.sleeps.lock().pending_count()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_clock_starts_at_zero() {
        let clock = MockClock::new();
        assert_eq!(clock.now(), Duration::ZERO);
    }

    #[test]
    fn test_with_start_time() {
        let clock = MockClock::with_start_time(Duration::from_secs(100));
        assert_eq!(clock.now(), Duration::from_secs(100));
    }

    #[test]
    fn test_advance() {
        let clock = MockClock::new();
        clock.advance(Duration::from_secs(10));
        assert_eq!(clock.now(), Duration::from_secs(10));

        clock.advance(Duration::from_secs(5));
        assert_eq!(clock.now(), Duration::from_secs(15));
    }

    #[test]
    fn test_set() {
        let clock = MockClock::new();
        clock.set(Duration::from_secs(100));
        assert_eq!(clock.now(), Duration::from_secs(100));

        // Can set to lower value
        clock.set(Duration::from_secs(50));
        assert_eq!(clock.now(), Duration::from_secs(50));
    }

    #[test]
    fn test_advance_to() {
        let clock = MockClock::new();
        clock.advance_to(Duration::from_secs(10));
        assert_eq!(clock.now(), Duration::from_secs(10));

        // Trying to advance to earlier time is no-op
        clock.advance_to(Duration::from_secs(5));
        assert_eq!(clock.now(), Duration::from_secs(10));

        // Can advance to later time
        clock.advance_to(Duration::from_secs(20));
        assert_eq!(clock.now(), Duration::from_secs(20));
    }

    #[test]
    fn test_elapsed() {
        let clock = MockClock::with_start_time(Duration::from_secs(100));
        assert_eq!(clock.elapsed(), Duration::from_secs(100));

        clock.advance(Duration::from_secs(50));
        assert_eq!(clock.elapsed(), Duration::from_secs(150));
    }

    #[test]
    fn test_pause_resume() {
        let clock = MockClock::new();
        assert!(!clock.is_paused());

        clock.pause();
        assert!(clock.is_paused());

        clock.resume();
        assert!(!clock.is_paused());
    }

    #[test]
    #[should_panic(expected = "Cannot advance time while clock is paused")]
    fn test_advance_while_paused_panics() {
        let clock = MockClock::new();
        clock.pause();
        clock.advance(Duration::from_secs(1));
    }

    #[test]
    #[should_panic(expected = "Cannot set time while clock is paused")]
    fn test_set_while_paused_panics() {
        let clock = MockClock::new();
        clock.pause();
        clock.set(Duration::from_secs(1));
    }

    #[test]
    #[should_panic(expected = "Cannot advance time while clock is paused")]
    fn test_advance_to_while_paused_panics() {
        let clock = MockClock::new();
        clock.pause();
        clock.advance_to(Duration::from_secs(1));
    }

    #[test]
    fn test_clone_shares_state() {
        let clock1 = MockClock::new();
        let clock2 = clock1.clone();

        clock1.advance(Duration::from_secs(10));
        assert_eq!(clock2.now(), Duration::from_secs(10));

        clock2.advance(Duration::from_secs(5));
        assert_eq!(clock1.now(), Duration::from_secs(15));
    }

    #[test]
    fn test_thread_safety() {
        use std::thread;

        let clock = MockClock::new();
        let clock2 = clock.clone();

        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                clock2.advance(Duration::from_millis(1));
            }
        });

        for _ in 0..1000 {
            clock.advance(Duration::from_millis(1));
        }

        handle.join().unwrap();
        assert_eq!(clock.now(), Duration::from_millis(2000));
    }

    #[test]
    fn test_default() {
        let clock = MockClock::default();
        assert_eq!(clock.now(), Duration::ZERO);
    }
}
