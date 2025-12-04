//! Task types for the test executor.

use std::fmt;
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::task::{Context, Poll};

use parking_lot::Mutex;

/// Unique identifier for a spawned task.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TaskId(u64);

impl TaskId {
    /// Creates a new unique task ID.
    pub(crate) fn new() -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        Self(COUNTER.fetch_add(1, Ordering::Relaxed))
    }

    /// Returns the raw ID value.
    #[must_use]
    pub fn as_u64(&self) -> u64 {
        self.0
    }
}

impl fmt::Display for TaskId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Task({})", self.0)
    }
}

/// The current state of a task.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TaskState {
    /// Task is waiting to be polled.
    Pending,
    /// Task is currently being polled.
    Running,
    /// Task completed successfully.
    Completed,
    /// Task was cancelled.
    Cancelled,
}

impl fmt::Display for TaskState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TaskState::Pending => write!(f, "Pending"),
            TaskState::Running => write!(f, "Running"),
            TaskState::Completed => write!(f, "Completed"),
            TaskState::Cancelled => write!(f, "Cancelled"),
        }
    }
}

/// Information about a task.
#[derive(Clone, Debug)]
pub struct TaskInfo {
    /// The task's unique identifier.
    pub id: TaskId,
    /// Current state of the task.
    pub state: TaskState,
    /// Optional name for debugging.
    pub name: Option<String>,
    /// Number of times this task has been polled.
    pub poll_count: usize,
}

impl TaskInfo {
    /// Creates new task info.
    pub(crate) fn new(id: TaskId) -> Self {
        Self {
            id,
            state: TaskState::Pending,
            name: None,
            poll_count: 0,
        }
    }

    /// Sets a name for the task.
    #[must_use]
    pub fn with_name(mut self, name: impl Into<String>) -> Self {
        self.name = Some(name.into());
        self
    }
}

/// Handle to a spawned task.
///
/// This handle can be used to check the task's status or retrieve its result.
pub struct TaskHandle<T> {
    /// The task's unique identifier.
    pub id: TaskId,
    /// Shared state for retrieving the result.
    result: Arc<Mutex<Option<T>>>,
}

impl<T> TaskHandle<T> {
    /// Creates a new task handle.
    pub(crate) fn new(id: TaskId, result: Arc<Mutex<Option<T>>>) -> Self {
        Self { id, result }
    }

    /// Tries to get the result if the task has completed.
    ///
    /// Returns `None` if the task hasn't completed yet.
    #[must_use]
    pub fn try_get(&self) -> Option<T>
    where
        T: Clone,
    {
        self.result.lock().clone()
    }

    /// Takes the result if the task has completed.
    ///
    /// Returns `None` if the task hasn't completed yet or the result was already taken.
    #[must_use]
    pub fn take(&self) -> Option<T> {
        self.result.lock().take()
    }

    /// Returns true if the task has completed.
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.result.lock().is_some()
    }
}

impl<T> Clone for TaskHandle<T> {
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            result: Arc::clone(&self.result),
        }
    }
}

impl<T> fmt::Debug for TaskHandle<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TaskHandle")
            .field("id", &self.id)
            .field("is_complete", &self.is_complete())
            .finish_non_exhaustive()
    }
}

/// Type-erased boxed future.
pub(crate) type BoxFuture = Pin<Box<dyn Future<Output = ()> + Send>>;

/// Internal task representation.
pub(crate) struct Task {
    pub id: TaskId,
    pub future: BoxFuture,
    pub info: TaskInfo,
}

impl Task {
    /// Creates a new task wrapping a future.
    pub fn new<F, T>(future: F, result_slot: Arc<Mutex<Option<T>>>) -> Self
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        let id = TaskId::new();
        let info = TaskInfo::new(id);

        // Wrap the future to store the result when complete
        let wrapped = async move {
            let output = future.await;
            *result_slot.lock() = Some(output);
        };

        Self {
            id,
            future: Box::pin(wrapped),
            info,
        }
    }

    /// Polls the task once.
    ///
    /// Returns `Poll::Ready(())` if the task completed.
    pub fn poll(&mut self, cx: &mut Context<'_>) -> Poll<()> {
        self.info.state = TaskState::Running;
        self.info.poll_count += 1;

        match self.future.as_mut().poll(cx) {
            Poll::Ready(()) => {
                self.info.state = TaskState::Completed;
                Poll::Ready(())
            }
            Poll::Pending => {
                self.info.state = TaskState::Pending;
                Poll::Pending
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_task_id_unique() {
        let id1 = TaskId::new();
        let id2 = TaskId::new();
        let id3 = TaskId::new();

        assert_ne!(id1, id2);
        assert_ne!(id2, id3);
        assert_ne!(id1, id3);
    }

    #[test]
    fn test_task_id_ordering() {
        let id1 = TaskId::new();
        let id2 = TaskId::new();

        assert!(id1 < id2);
    }

    #[test]
    fn test_task_state_display() {
        assert_eq!(TaskState::Pending.to_string(), "Pending");
        assert_eq!(TaskState::Running.to_string(), "Running");
        assert_eq!(TaskState::Completed.to_string(), "Completed");
        assert_eq!(TaskState::Cancelled.to_string(), "Cancelled");
    }

    #[test]
    fn test_task_info_with_name() {
        let id = TaskId::new();
        let info = TaskInfo::new(id).with_name("my-task");

        assert_eq!(info.name, Some("my-task".to_string()));
        assert_eq!(info.state, TaskState::Pending);
        assert_eq!(info.poll_count, 0);
    }

    #[test]
    fn test_task_handle_initially_incomplete() {
        let result: Arc<Mutex<Option<i32>>> = Arc::new(Mutex::new(None));
        let handle = TaskHandle::new(TaskId::new(), result);

        assert!(!handle.is_complete());
        assert!(handle.try_get().is_none());
    }

    #[test]
    fn test_task_handle_complete() {
        let result: Arc<Mutex<Option<i32>>> = Arc::new(Mutex::new(Some(42)));
        let handle = TaskHandle::new(TaskId::new(), result);

        assert!(handle.is_complete());
        assert_eq!(handle.try_get(), Some(42));
    }

    #[test]
    fn test_task_handle_take() {
        let result: Arc<Mutex<Option<i32>>> = Arc::new(Mutex::new(Some(42)));
        let handle = TaskHandle::new(TaskId::new(), result);

        assert_eq!(handle.take(), Some(42));
        assert!(handle.take().is_none()); // Can only take once
    }
}
