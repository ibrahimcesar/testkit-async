//! Sync points for task coordination.
//!
//! Sync points allow precise coordination between concurrent tasks.
//! Tasks can wait at named points until explicitly released.

use std::collections::HashMap;
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context, Poll, Waker};

use parking_lot::Mutex;

/// Shared state for sync points.
#[derive(Default)]
pub(crate) struct SyncPointState {
    /// Map of sync point names to waiting wakers.
    points: Mutex<HashMap<String, Vec<Waker>>>,
}

impl SyncPointState {
    /// Creates a new sync point state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Registers a waker at the named sync point.
    pub fn register(&self, name: &str, waker: Waker) {
        let mut points = self.points.lock();
        points.entry(name.to_string()).or_default().push(waker);
    }

    /// Releases all tasks waiting at the named sync point.
    ///
    /// Returns the number of tasks released.
    pub fn release(&self, name: &str) -> usize {
        let mut points = self.points.lock();
        if let Some(wakers) = points.remove(name) {
            let count = wakers.len();
            for waker in wakers {
                waker.wake();
            }
            count
        } else {
            0
        }
    }

    /// Releases one task waiting at the named sync point.
    ///
    /// Returns `true` if a task was released.
    pub fn release_one(&self, name: &str) -> bool {
        let mut points = self.points.lock();
        if let Some(wakers) = points.get_mut(name) {
            if let Some(waker) = wakers.pop() {
                waker.wake();
                // Remove the entry if no more wakers
                if wakers.is_empty() {
                    points.remove(name);
                }
                return true;
            }
        }
        false
    }

    /// Returns the number of tasks waiting at the named sync point.
    #[must_use]
    pub fn waiting_at(&self, name: &str) -> usize {
        let points = self.points.lock();
        points.get(name).map_or(0, Vec::len)
    }
}

/// A future that waits at a named sync point.
pub struct SyncPointFuture {
    name: String,
    state: Arc<SyncPointState>,
    registered: bool,
}

impl SyncPointFuture {
    /// Creates a new sync point future.
    pub(crate) fn new(name: String, state: Arc<SyncPointState>) -> Self {
        Self {
            name,
            state,
            registered: false,
        }
    }
}

impl Future for SyncPointFuture {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.registered {
            // We were woken - sync point was released
            Poll::Ready(())
        } else {
            // First poll - register ourselves
            self.state.register(&self.name, cx.waker().clone());
            self.registered = true;
            Poll::Pending
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sync_point_state_new() {
        let state = SyncPointState::new();
        assert_eq!(state.waiting_at("test"), 0);
    }

    #[test]
    fn test_sync_point_register_and_waiting() {
        let state = SyncPointState::new();
        let waker = futures::task::noop_waker();

        state.register("checkpoint", waker.clone());
        assert_eq!(state.waiting_at("checkpoint"), 1);

        state.register("checkpoint", waker.clone());
        assert_eq!(state.waiting_at("checkpoint"), 2);

        state.register("other", waker);
        assert_eq!(state.waiting_at("other"), 1);
    }

    #[test]
    fn test_sync_point_release_all() {
        let state = SyncPointState::new();
        let waker = futures::task::noop_waker();

        state.register("checkpoint", waker.clone());
        state.register("checkpoint", waker.clone());
        state.register("checkpoint", waker);

        let released = state.release("checkpoint");
        assert_eq!(released, 3);
        assert_eq!(state.waiting_at("checkpoint"), 0);
    }

    #[test]
    fn test_sync_point_release_one() {
        let state = SyncPointState::new();
        let waker = futures::task::noop_waker();

        state.register("checkpoint", waker.clone());
        state.register("checkpoint", waker);

        assert!(state.release_one("checkpoint"));
        assert_eq!(state.waiting_at("checkpoint"), 1);

        assert!(state.release_one("checkpoint"));
        assert_eq!(state.waiting_at("checkpoint"), 0);

        assert!(!state.release_one("checkpoint"));
    }

    #[test]
    fn test_sync_point_release_nonexistent() {
        let state = SyncPointState::new();
        assert_eq!(state.release("nonexistent"), 0);
        assert!(!state.release_one("nonexistent"));
    }
}
