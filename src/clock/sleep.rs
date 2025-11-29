//! Mock sleep and delay futures.

use pin_project::pin_project;
use std::collections::BinaryHeap;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};
use std::time::Duration;

use super::MockClock;

/// A pending sleep entry in the sleep queue.
#[derive(Debug)]
struct SleepEntry {
    /// The deadline when this sleep should complete
    deadline: Duration,
    /// The waker to wake when the deadline is reached
    waker: Option<Waker>,
    /// Unique ID for this sleep (for ordering)
    id: u64,
}

impl PartialEq for SleepEntry {
    fn eq(&self, other: &Self) -> bool {
        self.deadline == other.deadline && self.id == other.id
    }
}

impl Eq for SleepEntry {}

impl PartialOrd for SleepEntry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SleepEntry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Reverse order for min-heap behavior (earliest deadline first)
        other
            .deadline
            .cmp(&self.deadline)
            .then_with(|| other.id.cmp(&self.id))
    }
}

/// Internal state for managing sleeps.
#[derive(Debug)]
pub(crate) struct SleepState {
    /// Priority queue of pending sleeps (min-heap by deadline)
    pending: BinaryHeap<SleepEntry>,
    /// Counter for generating unique sleep IDs
    next_id: u64,
}

impl SleepState {
    pub(crate) fn new() -> Self {
        Self {
            pending: BinaryHeap::new(),
            next_id: 0,
        }
    }

    /// Register a new sleep and return its ID
    fn register(&mut self, deadline: Duration) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        self.pending.push(SleepEntry {
            deadline,
            waker: None,
            id,
        });
        id
    }

    /// Update the waker for a sleep
    fn update_waker(&mut self, id: u64, waker: &Waker) {
        // Find and update the entry with matching ID
        let entries: Vec<_> = self.pending.drain().collect();
        for mut entry in entries {
            if entry.id == id {
                entry.waker = Some(waker.clone());
            }
            self.pending.push(entry);
        }
    }

    /// Wake all sleeps whose deadline has passed
    pub(crate) fn wake_expired(&mut self, current_time: Duration) {
        while let Some(entry) = self.pending.peek() {
            if entry.deadline <= current_time {
                if let Some(waker) = self.pending.pop().and_then(|e| e.waker) {
                    waker.wake();
                }
            } else {
                break;
            }
        }
    }

    /// Remove a sleep entry
    fn remove(&mut self, id: u64) {
        let entries: Vec<_> = self.pending.drain().filter(|e| e.id != id).collect();
        for entry in entries {
            self.pending.push(entry);
        }
    }

    /// Get the number of pending sleeps
    pub(crate) fn pending_count(&self) -> usize {
        self.pending.len()
    }
}

/// A future that completes when virtual time advances past its deadline.
///
/// Created by [`MockClock::sleep`].
#[pin_project]
#[derive(Debug)]
pub struct MockSleep {
    clock: MockClock,
    deadline: Duration,
    id: u64,
    registered: bool,
}

impl MockSleep {
    pub(crate) fn new(clock: MockClock, duration: Duration) -> Self {
        let deadline = clock.now() + duration;
        Self {
            clock,
            deadline,
            id: 0,
            registered: false,
        }
    }

    /// Returns the deadline for this sleep.
    #[must_use]
    pub fn deadline(&self) -> Duration {
        self.deadline
    }

    /// Returns the remaining time until this sleep completes.
    ///
    /// Returns `Duration::ZERO` if the deadline has already passed.
    #[must_use]
    pub fn remaining(&self) -> Duration {
        let now = self.clock.now();
        if self.deadline > now {
            self.deadline - now
        } else {
            Duration::ZERO
        }
    }

    /// Returns `true` if this sleep has completed.
    #[must_use]
    pub fn is_elapsed(&self) -> bool {
        self.clock.now() >= self.deadline
    }
}

impl Future for MockSleep {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();

        // Register the sleep if not already done
        if !*this.registered {
            let mut sleeps = this.clock.inner.sleeps.lock();
            *this.id = sleeps.register(*this.deadline);
            *this.registered = true;
        }

        // Check if we've passed the deadline
        if this.clock.now() >= *this.deadline {
            // Remove ourselves from pending sleeps
            let mut sleeps = this.clock.inner.sleeps.lock();
            sleeps.remove(*this.id);
            Poll::Ready(())
        } else {
            // Update our waker and wait
            let mut sleeps = this.clock.inner.sleeps.lock();
            sleeps.update_waker(*this.id, cx.waker());
            Poll::Pending
        }
    }
}

/// A future that completes after a virtual delay.
///
/// This is similar to [`MockSleep`] but can be reset.
#[pin_project]
#[derive(Debug)]
pub struct MockDelay {
    #[pin]
    inner: MockSleep,
}

impl MockDelay {
    pub(crate) fn new(clock: MockClock, duration: Duration) -> Self {
        Self {
            inner: MockSleep::new(clock, duration),
        }
    }

    /// Returns the deadline for this delay.
    #[must_use]
    pub fn deadline(&self) -> Duration {
        self.inner.deadline()
    }

    /// Returns `true` if this delay has elapsed.
    #[must_use]
    pub fn is_elapsed(&self) -> bool {
        self.inner.is_elapsed()
    }
}

impl Future for MockDelay {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.project().inner.poll(cx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sleep_state_register() {
        let mut state = SleepState::new();
        let id1 = state.register(Duration::from_secs(10));
        let id2 = state.register(Duration::from_secs(5));
        let id3 = state.register(Duration::from_secs(15));

        assert_eq!(id1, 0);
        assert_eq!(id2, 1);
        assert_eq!(id3, 2);
        assert_eq!(state.pending_count(), 3);
    }

    #[test]
    fn test_sleep_state_ordering() {
        let mut state = SleepState::new();
        state.register(Duration::from_secs(10));
        state.register(Duration::from_secs(5));
        state.register(Duration::from_secs(15));

        // Should be ordered by deadline (earliest first)
        let first = state.pending.peek().unwrap();
        assert_eq!(first.deadline, Duration::from_secs(5));
    }

    #[test]
    fn test_sleep_state_wake_expired() {
        let mut state = SleepState::new();
        state.register(Duration::from_secs(5));
        state.register(Duration::from_secs(10));
        state.register(Duration::from_secs(15));

        // Wake sleeps up to 10 seconds
        state.wake_expired(Duration::from_secs(10));

        // Only the 15-second sleep should remain
        assert_eq!(state.pending_count(), 1);
        assert_eq!(
            state.pending.peek().unwrap().deadline,
            Duration::from_secs(15)
        );
    }

    #[test]
    fn test_mock_sleep_deadline() {
        let clock = MockClock::new();
        let sleep = MockSleep::new(clock.clone(), Duration::from_secs(10));

        assert_eq!(sleep.deadline(), Duration::from_secs(10));
        assert_eq!(sleep.remaining(), Duration::from_secs(10));
        assert!(!sleep.is_elapsed());

        clock.advance(Duration::from_secs(5));
        assert_eq!(sleep.remaining(), Duration::from_secs(5));
        assert!(!sleep.is_elapsed());

        clock.advance(Duration::from_secs(5));
        assert_eq!(sleep.remaining(), Duration::ZERO);
        assert!(sleep.is_elapsed());
    }

    #[tokio::test]
    async fn test_mock_sleep_completes_on_advance() {
        use std::sync::atomic::{AtomicBool, Ordering};
        use std::sync::Arc;

        let clock = MockClock::new();
        let completed = Arc::new(AtomicBool::new(false));
        let completed2 = completed.clone();

        // Spawn a task that sleeps
        let clock2 = clock.clone();
        let handle = tokio::spawn(async move {
            clock2.sleep(Duration::from_secs(10)).await;
            completed2.store(true, Ordering::SeqCst);
        });

        // Give the task a chance to start
        tokio::task::yield_now().await;

        // Sleep hasn't completed yet
        assert!(!completed.load(Ordering::SeqCst));

        // Advance time past the deadline
        clock.advance(Duration::from_secs(10));

        // Wait for the task to complete
        handle.await.unwrap();

        // Sleep completed!
        assert!(completed.load(Ordering::SeqCst));
    }

    #[tokio::test]
    async fn test_multiple_sleeps_wake_in_order() {
        use std::sync::atomic::{AtomicU32, Ordering};
        use std::sync::Arc;

        let clock = MockClock::new();
        let order = Arc::new(AtomicU32::new(0));

        let order1 = order.clone();
        let clock1 = clock.clone();
        let h1 = tokio::spawn(async move {
            clock1.sleep(Duration::from_secs(5)).await;
            order1.fetch_add(1, Ordering::SeqCst);
        });

        let order2 = order.clone();
        let clock2 = clock.clone();
        let h2 = tokio::spawn(async move {
            clock2.sleep(Duration::from_secs(10)).await;
            order2.fetch_add(10, Ordering::SeqCst);
        });

        // Let tasks start
        tokio::task::yield_now().await;
        tokio::task::yield_now().await;

        // Advance to 5 seconds - first sleep completes
        clock.advance(Duration::from_secs(5));
        h1.await.unwrap();
        assert_eq!(order.load(Ordering::SeqCst), 1);

        // Advance to 10 seconds - second sleep completes
        clock.advance(Duration::from_secs(5));
        h2.await.unwrap();
        assert_eq!(order.load(Ordering::SeqCst), 11);
    }
}
