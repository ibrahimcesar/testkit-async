//! The `TestExecutor` implementation.

use std::collections::VecDeque;
use std::future::Future;
use std::sync::Arc;
use std::task::{Context, Poll, Wake, Waker};

use parking_lot::Mutex;

use crate::executor::task::{Task, TaskHandle, TaskId, TaskInfo, TaskState};

/// A test executor that provides deterministic task execution.
///
/// Unlike production executors, `TestExecutor` doesn't run tasks automatically.
/// Instead, you manually control when tasks execute using methods like [`step`]
/// and [`run_until_stalled`].
///
/// # Example
///
/// ```rust
/// use testkit_async::executor::TestExecutor;
///
/// let executor = TestExecutor::new();
///
/// // Spawn a task
/// let handle = executor.spawn(async { 42 });
///
/// // Task hasn't run yet
/// assert!(!handle.is_complete());
///
/// // Run the task
/// executor.step();
///
/// // Now we can get the result
/// assert_eq!(handle.take(), Some(42));
/// ```
///
/// [`step`]: TestExecutor::step
/// [`run_until_stalled`]: TestExecutor::run_until_stalled
#[derive(Clone)]
pub struct TestExecutor {
    inner: Arc<ExecutorInner>,
}

struct ExecutorInner {
    /// Queue of tasks ready to be polled.
    ready_queue: Mutex<VecDeque<Task>>,
    /// Tasks that are waiting (returned Pending).
    waiting: Mutex<Vec<Task>>,
    /// Information about all tasks (for inspection).
    task_info: Mutex<Vec<TaskInfo>>,
}

impl TestExecutor {
    /// Creates a new test executor.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::executor::TestExecutor;
    ///
    /// let executor = TestExecutor::new();
    /// assert_eq!(executor.pending_count(), 0);
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self {
            inner: Arc::new(ExecutorInner {
                ready_queue: Mutex::new(VecDeque::new()),
                waiting: Mutex::new(Vec::new()),
                task_info: Mutex::new(Vec::new()),
            }),
        }
    }

    /// Spawns a future on this executor.
    ///
    /// The future will not run until you call [`step`], [`run_until_stalled`],
    /// or another execution method.
    ///
    /// Returns a [`TaskHandle`] that can be used to retrieve the result.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::executor::TestExecutor;
    ///
    /// let executor = TestExecutor::new();
    ///
    /// let handle = executor.spawn(async {
    ///     1 + 1
    /// });
    ///
    /// assert_eq!(executor.pending_count(), 1);
    /// ```
    ///
    /// [`step`]: TestExecutor::step
    /// [`run_until_stalled`]: TestExecutor::run_until_stalled
    pub fn spawn<F, T>(&self, future: F) -> TaskHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        let result_slot = Arc::new(Mutex::new(None));
        let task = Task::new(future, Arc::clone(&result_slot));
        let id = task.id;
        let info = task.info.clone();

        // Store task info for inspection
        self.inner.task_info.lock().push(info);

        // Add to ready queue
        self.inner.ready_queue.lock().push_back(task);

        TaskHandle::new(id, result_slot)
    }

    /// Returns the number of tasks that are ready to run.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::executor::TestExecutor;
    ///
    /// let executor = TestExecutor::new();
    /// executor.spawn(async { 1 });
    /// executor.spawn(async { 2 });
    ///
    /// assert_eq!(executor.pending_count(), 2);
    /// ```
    #[must_use]
    pub fn pending_count(&self) -> usize {
        self.inner.ready_queue.lock().len()
    }

    /// Returns the number of tasks waiting (returned `Poll::Pending`).
    #[must_use]
    pub fn waiting_count(&self) -> usize {
        self.inner.waiting.lock().len()
    }

    /// Returns the total number of active tasks (pending + waiting).
    #[must_use]
    pub fn active_count(&self) -> usize {
        self.pending_count() + self.waiting_count()
    }

    /// Returns true if there are no active tasks.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.active_count() == 0
    }

    /// Gets information about a task by its ID.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::executor::{TestExecutor, TaskState};
    ///
    /// let executor = TestExecutor::new();
    /// let handle = executor.spawn(async { 42 });
    ///
    /// let info = executor.task(handle.id).unwrap();
    /// assert_eq!(info.state, TaskState::Pending);
    /// ```
    #[must_use]
    pub fn task(&self, id: TaskId) -> Option<TaskInfo> {
        self.inner
            .task_info
            .lock()
            .iter()
            .find(|info| info.id == id)
            .cloned()
    }

    /// Returns information about all tasks.
    #[must_use]
    pub fn tasks(&self) -> Vec<TaskInfo> {
        self.inner.task_info.lock().clone()
    }

    /// Executes one step: polls a single task from the ready queue.
    ///
    /// Returns `true` if a task was polled, `false` if the ready queue was empty.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::executor::TestExecutor;
    ///
    /// let executor = TestExecutor::new();
    /// let handle = executor.spawn(async { 42 });
    ///
    /// // Step once to run the task
    /// assert!(executor.step());
    ///
    /// // Task is now complete
    /// assert_eq!(handle.take(), Some(42));
    ///
    /// // No more tasks to run
    /// assert!(!executor.step());
    /// ```
    #[must_use]
    pub fn step(&self) -> bool {
        let task = self.inner.ready_queue.lock().pop_front();

        if let Some(mut task) = task {
            let (waker, woken_flag) = self.create_waker(task.id);
            let mut cx = Context::from_waker(&waker);

            match task.poll(&mut cx) {
                Poll::Ready(()) => {
                    // Task completed - update info
                    self.update_task_info(task.id, |info| {
                        info.state = TaskState::Completed;
                        info.poll_count = task.info.poll_count;
                    });
                }
                Poll::Pending => {
                    // Check if task was woken during poll
                    let was_woken = *woken_flag.lock();
                    self.update_task_info(task.id, |info| {
                        info.state = TaskState::Pending;
                        info.poll_count = task.info.poll_count;
                    });

                    if was_woken {
                        // Task woke itself - put back in ready queue
                        self.inner.ready_queue.lock().push_back(task);
                    } else {
                        // Task is waiting for external wake
                        self.inner.waiting.lock().push(task);
                    }
                }
            }
            true
        } else {
            false
        }
    }

    /// Runs all ready tasks until none are ready.
    ///
    /// This will keep polling tasks until the ready queue is empty.
    /// Note that tasks which return `Poll::Pending` are moved to the
    /// waiting list and won't be re-polled until woken.
    ///
    /// Returns the number of times tasks were polled.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::executor::TestExecutor;
    ///
    /// let executor = TestExecutor::new();
    /// executor.spawn(async { 1 });
    /// executor.spawn(async { 2 });
    /// executor.spawn(async { 3 });
    ///
    /// // Run all three tasks
    /// let polls = executor.run_until_stalled();
    /// assert_eq!(polls, 3);
    /// assert_eq!(executor.pending_count(), 0);
    /// ```
    #[must_use]
    pub fn run_until_stalled(&self) -> usize {
        let mut count = 0;
        while self.step() {
            count += 1;
        }
        count
    }

    /// Wakes a task, moving it from the waiting list to the ready queue.
    ///
    /// Returns `true` if the task was found and woken.
    #[must_use]
    pub fn wake(&self, id: TaskId) -> bool {
        let mut waiting = self.inner.waiting.lock();
        if let Some(pos) = waiting.iter().position(|t| t.id == id) {
            let task = waiting.remove(pos);
            self.inner.ready_queue.lock().push_back(task);
            true
        } else {
            false
        }
    }

    /// Wakes all waiting tasks.
    ///
    /// Returns the number of tasks woken.
    #[must_use]
    pub fn wake_all(&self) -> usize {
        let mut waiting = self.inner.waiting.lock();
        let mut ready = self.inner.ready_queue.lock();

        let count = waiting.len();
        ready.extend(waiting.drain(..));
        count
    }

    /// Creates a waker for a task with a shared wake flag.
    fn create_waker(&self, id: TaskId) -> (Waker, Arc<Mutex<bool>>) {
        let woken_flag = Arc::new(Mutex::new(false));
        let waker = TaskWaker {
            executor: Arc::clone(&self.inner),
            id,
            woken_during_poll: Arc::clone(&woken_flag),
        };
        (Waker::from(Arc::new(waker)), woken_flag)
    }

    /// Updates task info by ID.
    fn update_task_info<F>(&self, id: TaskId, f: F)
    where
        F: FnOnce(&mut TaskInfo),
    {
        let mut infos = self.inner.task_info.lock();
        if let Some(info) = infos.iter_mut().find(|i| i.id == id) {
            f(info);
        }
    }
}

impl Default for TestExecutor {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for TestExecutor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TestExecutor")
            .field("pending", &self.pending_count())
            .field("waiting", &self.waiting_count())
            .finish()
    }
}

/// Waker implementation that re-queues tasks.
struct TaskWaker {
    executor: Arc<ExecutorInner>,
    id: TaskId,
    /// Flag to indicate this task should be re-queued after poll
    woken_during_poll: Arc<Mutex<bool>>,
}

impl Wake for TaskWaker {
    fn wake(self: Arc<Self>) {
        self.wake_by_ref();
    }

    fn wake_by_ref(self: &Arc<Self>) {
        // Try to move task from waiting to ready
        let mut waiting = self.executor.waiting.lock();
        if let Some(pos) = waiting.iter().position(|t| t.id == self.id) {
            let task = waiting.remove(pos);
            self.executor.ready_queue.lock().push_back(task);
        } else {
            // Task not in waiting - might be currently being polled
            // Set flag so it gets re-queued after poll
            *self.woken_during_poll.lock() = true;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_executor_is_empty() {
        let executor = TestExecutor::new();
        assert!(executor.is_empty());
        assert_eq!(executor.pending_count(), 0);
        assert_eq!(executor.waiting_count(), 0);
    }

    #[test]
    fn test_spawn_adds_to_pending() {
        let executor = TestExecutor::new();
        let _handle = executor.spawn(async { 42 });

        assert_eq!(executor.pending_count(), 1);
        assert!(!executor.is_empty());
    }

    #[test]
    fn test_step_runs_task() {
        let executor = TestExecutor::new();
        let handle = executor.spawn(async { 42 });

        assert!(!handle.is_complete());
        assert!(executor.step());
        assert!(handle.is_complete());
        assert_eq!(handle.take(), Some(42));
    }

    #[test]
    fn test_step_returns_false_when_empty() {
        let executor = TestExecutor::new();
        assert!(!executor.step());
    }

    #[test]
    fn test_run_until_stalled() {
        let executor = TestExecutor::new();
        executor.spawn(async { 1 });
        executor.spawn(async { 2 });
        executor.spawn(async { 3 });

        let polls = executor.run_until_stalled();
        assert_eq!(polls, 3);
        assert_eq!(executor.pending_count(), 0);
    }

    #[test]
    fn test_task_info() {
        let executor = TestExecutor::new();
        let handle = executor.spawn(async { 42 });

        let info = executor.task(handle.id).unwrap();
        assert_eq!(info.id, handle.id);
        assert_eq!(info.state, TaskState::Pending);
        assert_eq!(info.poll_count, 0);

        let _ = executor.step();

        let info = executor.task(handle.id).unwrap();
        assert_eq!(info.state, TaskState::Completed);
        assert_eq!(info.poll_count, 1);
    }

    #[test]
    fn test_task_requiring_multiple_polls() {
        let executor = TestExecutor::new();

        // Spawn a task that yields once before completing
        let handle = executor.spawn(std::future::pending::<()>());

        // First poll - task yields
        let _ = executor.step();
        assert!(!handle.is_complete());
        assert_eq!(executor.waiting_count(), 1);

        // Manually wake the task
        assert!(executor.wake(handle.id));
        assert_eq!(executor.pending_count(), 1);
        assert_eq!(executor.waiting_count(), 0);
    }

    #[test]
    fn test_task_poll_count() {
        use std::cell::Cell;
        use std::pin::Pin;
        use std::task::{Context, Poll};

        // A future that tracks how many times it's been polled
        struct CountingFuture {
            polls: Cell<usize>,
            complete_after: usize,
        }

        impl std::future::Future for CountingFuture {
            type Output = usize;

            fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
                let count = self.polls.get() + 1;
                self.polls.set(count);

                if count >= self.complete_after {
                    Poll::Ready(count)
                } else {
                    // Wake ourselves so we get polled again
                    cx.waker().wake_by_ref();
                    Poll::Pending
                }
            }
        }

        let executor = TestExecutor::new();
        let handle = executor.spawn(CountingFuture {
            polls: Cell::new(0),
            complete_after: 3,
        });

        // Run until the task completes
        let _ = executor.run_until_stalled();

        assert!(handle.is_complete());
        assert_eq!(handle.take(), Some(3));
        // Task was polled 3 times total
        let info = executor.task(handle.id).unwrap();
        assert_eq!(info.poll_count, 3);
        assert_eq!(info.state, TaskState::Completed);
    }

    #[test]
    fn test_wake_all() {
        let executor = TestExecutor::new();

        // Spawn tasks that immediately yield
        executor.spawn(std::future::pending::<()>());
        executor.spawn(std::future::pending::<()>());
        executor.spawn(std::future::pending::<()>());

        // Run them - they all move to waiting
        let _ = executor.run_until_stalled();
        assert_eq!(executor.waiting_count(), 3);
        assert_eq!(executor.pending_count(), 0);

        // Wake all
        let woken = executor.wake_all();
        assert_eq!(woken, 3);
        assert_eq!(executor.pending_count(), 3);
        assert_eq!(executor.waiting_count(), 0);
    }

    #[test]
    fn test_executor_clone_shares_state() {
        let executor1 = TestExecutor::new();
        let executor2 = executor1.clone();

        let handle = executor1.spawn(async { 42 });
        assert_eq!(executor2.pending_count(), 1);

        let _ = executor2.step();
        assert!(handle.is_complete());
    }

    #[test]
    fn test_tasks_list() {
        let executor = TestExecutor::new();
        executor.spawn(async { 1 });
        executor.spawn(async { 2 });
        executor.spawn(async { 3 });

        let tasks = executor.tasks();
        assert_eq!(tasks.len(), 3);
    }

    #[test]
    fn test_default() {
        let executor = TestExecutor::default();
        assert!(executor.is_empty());
    }

    #[test]
    fn test_debug() {
        let executor = TestExecutor::new();
        executor.spawn(async { 1 });
        let debug = format!("{:?}", executor);
        assert!(debug.contains("TestExecutor"));
        assert!(debug.contains("pending"));
    }
}
