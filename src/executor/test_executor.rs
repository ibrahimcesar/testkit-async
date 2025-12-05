//! The `TestExecutor` implementation.

use std::collections::VecDeque;
use std::future::Future;
use std::sync::Arc;
use std::task::{Context, Poll, Wake, Waker};

use parking_lot::Mutex;

use crate::executor::sync_point::{SyncPointFuture, SyncPointState};
use crate::executor::task::{SchedulingPolicy, Task, TaskHandle, TaskId, TaskInfo, TaskState};

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
    /// Sync point coordination.
    sync_points: Arc<SyncPointState>,
    /// Scheduling policy for task ordering.
    policy: SchedulingPolicy,
    /// Random state for seeded scheduling.
    random_state: Mutex<u64>,
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
        Self::with_policy(SchedulingPolicy::Fifo)
    }

    /// Creates a new executor with the specified scheduling policy.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::executor::{TestExecutor, SchedulingPolicy};
    ///
    /// // Reproducible random ordering
    /// let executor = TestExecutor::with_policy(SchedulingPolicy::SeededRandom(42));
    /// ```
    #[must_use]
    pub fn with_policy(policy: SchedulingPolicy) -> Self {
        let seed = match &policy {
            SchedulingPolicy::SeededRandom(s) => *s,
            _ => 0,
        };
        Self {
            inner: Arc::new(ExecutorInner {
                ready_queue: Mutex::new(VecDeque::new()),
                waiting: Mutex::new(Vec::new()),
                task_info: Mutex::new(Vec::new()),
                sync_points: Arc::new(SyncPointState::new()),
                policy,
                random_state: Mutex::new(seed),
            }),
        }
    }

    /// Returns the scheduling policy being used.
    #[must_use]
    pub fn policy(&self) -> &SchedulingPolicy {
        &self.inner.policy
    }

    /// Returns the current random seed (for `SeededRandom` policy).
    #[must_use]
    pub fn seed(&self) -> u64 {
        *self.inner.random_state.lock()
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
        let task = self.next_task();

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

    // ========================================================================
    // Sync Points (Issue #8)
    // ========================================================================

    /// Creates a future that waits at the named sync point.
    ///
    /// Tasks will pause at sync points until explicitly released using
    /// [`release`] or [`release_one`].
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::executor::TestExecutor;
    ///
    /// let executor = TestExecutor::new();
    ///
    /// let sync = executor.sync_point("checkpoint");
    /// executor.spawn(async move {
    ///     sync.await;
    ///     42
    /// });
    ///
    /// executor.run_until_stalled();
    /// assert_eq!(executor.waiting_at("checkpoint"), 1);
    ///
    /// executor.release("checkpoint");
    /// executor.run_until_stalled();
    /// ```
    ///
    /// [`release`]: TestExecutor::release
    /// [`release_one`]: TestExecutor::release_one
    #[must_use]
    pub fn sync_point(&self, name: &str) -> SyncPointFuture {
        SyncPointFuture::new(name.to_string(), Arc::clone(&self.inner.sync_points))
    }

    /// Releases all tasks waiting at the named sync point.
    ///
    /// Returns the number of tasks released.
    #[must_use]
    pub fn release(&self, name: &str) -> usize {
        self.inner.sync_points.release(name)
    }

    /// Releases one task waiting at the named sync point.
    ///
    /// Returns `true` if a task was released.
    #[must_use]
    pub fn release_one(&self, name: &str) -> bool {
        self.inner.sync_points.release_one(name)
    }

    /// Returns the number of tasks waiting at the named sync point.
    #[must_use]
    pub fn waiting_at(&self, name: &str) -> usize {
        self.inner.sync_points.waiting_at(name)
    }

    // ========================================================================
    // Step-by-Step Execution (Issue #9)
    // ========================================================================

    /// Polls a specific task once.
    ///
    /// Returns `true` if the task was found and polled, `false` if not found.
    #[must_use]
    pub fn step_task(&self, id: TaskId) -> bool {
        // Try to find the task in the ready queue
        let task = {
            let mut ready = self.inner.ready_queue.lock();
            ready
                .iter()
                .position(|t| t.id == id)
                .and_then(|pos| ready.remove(pos))
        };

        if let Some(mut task) = task {
            let (waker, woken_flag) = self.create_waker(task.id);
            let mut cx = Context::from_waker(&waker);

            match task.poll(&mut cx) {
                Poll::Ready(()) => {
                    self.update_task_info(task.id, |info| {
                        info.state = TaskState::Completed;
                        info.poll_count = task.info.poll_count;
                    });
                }
                Poll::Pending => {
                    let was_woken = *woken_flag.lock();
                    self.update_task_info(task.id, |info| {
                        info.state = TaskState::Pending;
                        info.poll_count = task.info.poll_count;
                    });

                    if was_woken {
                        self.inner.ready_queue.lock().push_back(task);
                    } else {
                        self.inner.waiting.lock().push(task);
                    }
                }
            }
            true
        } else {
            false
        }
    }

    /// Runs for a limited number of steps.
    ///
    /// Returns the actual number of steps taken (may be less if all tasks complete).
    #[must_use]
    pub fn run_steps(&self, max_steps: usize) -> usize {
        let mut count = 0;
        while count < max_steps && self.step() {
            count += 1;
        }
        count
    }

    /// Runs until all tasks are complete.
    ///
    /// Returns the number of polls executed.
    ///
    /// # Panics
    ///
    /// Panics if the executor doesn't make progress (potential deadlock).
    #[must_use]
    pub fn run_until_complete(&self) -> usize {
        let mut count = 0;
        let max_iterations = 100_000;

        while self.active_count() > 0 {
            let stepped = self.step();
            if stepped {
                count += 1;
            } else if self.waiting_count() > 0 {
                // All tasks are blocked - this is a deadlock
                panic!(
                    "Deadlock detected: {} tasks waiting, none ready",
                    self.waiting_count()
                );
            }

            assert!(
                count <= max_iterations,
                "Executor ran for {max_iterations} iterations without completing"
            );
        }
        count
    }

    // ========================================================================
    // Task Inspection (Issue #10)
    // ========================================================================

    /// Spawns a named future on this executor.
    ///
    /// Named tasks are easier to debug and inspect.
    pub fn spawn_named<F, T>(&self, name: &str, future: F) -> TaskHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        let result_slot = Arc::new(Mutex::new(None));
        let mut task = Task::new(future, Arc::clone(&result_slot));
        task.info = task.info.with_name(name);
        let id = task.id;
        let info = task.info.clone();

        self.inner.task_info.lock().push(info);
        self.inner.ready_queue.lock().push_back(task);

        TaskHandle::new(id, result_slot)
    }

    /// Returns the number of completed tasks.
    #[must_use]
    pub fn completed_count(&self) -> usize {
        self.inner
            .task_info
            .lock()
            .iter()
            .filter(|t| t.state == TaskState::Completed)
            .count()
    }

    /// Finds a task by name.
    #[must_use]
    pub fn task_by_name(&self, name: &str) -> Option<TaskInfo> {
        self.inner
            .task_info
            .lock()
            .iter()
            .find(|t| t.name.as_deref() == Some(name))
            .cloned()
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

    /// Gets the next task based on the scheduling policy.
    fn next_task(&self) -> Option<Task> {
        let mut ready = self.inner.ready_queue.lock();
        if ready.is_empty() {
            return None;
        }

        match &self.inner.policy {
            SchedulingPolicy::Fifo => ready.pop_front(),
            SchedulingPolicy::Lifo => ready.pop_back(),
            SchedulingPolicy::SeededRandom(_) => {
                if ready.len() == 1 {
                    ready.pop_front()
                } else {
                    // Simple xorshift PRNG for reproducibility
                    let mut state = self.inner.random_state.lock();
                    let mut x = *state;
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    *state = x;

                    // Safe: we're taking modulo of ready.len() which is always small
                    #[allow(clippy::cast_possible_truncation)]
                    let idx = (x as usize) % ready.len();
                    ready.remove(idx)
                }
            }
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

    // ========================================================================
    // Sync Points Tests (Issue #8)
    // ========================================================================

    #[test]
    fn test_sync_point_basic() {
        let executor = TestExecutor::new();

        let sync = executor.sync_point("checkpoint");
        executor.spawn(async move {
            sync.await;
            42
        });

        // Run until task waits at sync point
        let _ = executor.run_until_stalled();
        assert_eq!(executor.waiting_at("checkpoint"), 1);
        assert_eq!(executor.waiting_count(), 1);

        // Release the sync point
        assert_eq!(executor.release("checkpoint"), 1);

        // Task should complete
        let _ = executor.run_until_stalled();
        assert_eq!(executor.waiting_at("checkpoint"), 0);
    }

    #[test]
    fn test_sync_point_multiple_tasks() {
        let executor = TestExecutor::new();

        let sync1 = executor.sync_point("checkpoint");
        let sync2 = executor.sync_point("checkpoint");
        let sync3 = executor.sync_point("checkpoint");

        executor.spawn(async move {
            sync1.await;
        });
        executor.spawn(async move {
            sync2.await;
        });
        executor.spawn(async move {
            sync3.await;
        });

        let _ = executor.run_until_stalled();
        assert_eq!(executor.waiting_at("checkpoint"), 3);

        // Release all at once
        let released = executor.release("checkpoint");
        assert_eq!(released, 3);

        let _ = executor.run_until_stalled();
        assert_eq!(executor.completed_count(), 3);
    }

    #[test]
    fn test_sync_point_release_one() {
        let executor = TestExecutor::new();

        let sync1 = executor.sync_point("checkpoint");
        let sync2 = executor.sync_point("checkpoint");

        executor.spawn(async move {
            sync1.await;
        });
        executor.spawn(async move {
            sync2.await;
        });

        let _ = executor.run_until_stalled();
        assert_eq!(executor.waiting_at("checkpoint"), 2);

        // Release one at a time
        assert!(executor.release_one("checkpoint"));
        let _ = executor.run_until_stalled();
        assert_eq!(executor.waiting_at("checkpoint"), 1);

        assert!(executor.release_one("checkpoint"));
        let _ = executor.run_until_stalled();
        assert_eq!(executor.waiting_at("checkpoint"), 0);

        // No more to release
        assert!(!executor.release_one("checkpoint"));
    }

    // ========================================================================
    // Step-by-Step Execution Tests (Issue #9)
    // ========================================================================

    #[test]
    fn test_step_task() {
        let executor = TestExecutor::new();

        let handle1 = executor.spawn(async { 1 });
        let handle2 = executor.spawn(async { 2 });

        // Step only the second task
        assert!(executor.step_task(handle2.id));
        assert!(handle2.is_complete());
        assert!(!handle1.is_complete());

        // Now step the first
        assert!(executor.step_task(handle1.id));
        assert!(handle1.is_complete());
    }

    #[test]
    fn test_step_task_not_found() {
        let executor = TestExecutor::new();
        let handle = executor.spawn(async { 1 });

        // Run the task first
        let _ = executor.step();

        // Task is no longer in ready queue
        assert!(!executor.step_task(handle.id));
    }

    #[test]
    fn test_run_steps() {
        let executor = TestExecutor::new();
        executor.spawn(async { 1 });
        executor.spawn(async { 2 });
        executor.spawn(async { 3 });
        executor.spawn(async { 4 });
        executor.spawn(async { 5 });

        // Only run 3 steps
        let stepped = executor.run_steps(3);
        assert_eq!(stepped, 3);
        assert_eq!(executor.pending_count(), 2);
    }

    #[test]
    fn test_run_until_complete() {
        let executor = TestExecutor::new();
        executor.spawn(async { 1 });
        executor.spawn(async { 2 });
        executor.spawn(async { 3 });

        let polls = executor.run_until_complete();
        assert_eq!(polls, 3);
        assert!(executor.is_empty());
    }

    // ========================================================================
    // Task Inspection Tests (Issue #10)
    // ========================================================================

    #[test]
    fn test_spawn_named() {
        let executor = TestExecutor::new();
        let handle = executor.spawn_named("my-task", async { 42 });

        let info = executor.task(handle.id).unwrap();
        assert_eq!(info.name, Some("my-task".to_string()));
    }

    #[test]
    fn test_task_by_name() {
        let executor = TestExecutor::new();
        executor.spawn_named("task-a", async { 1 });
        executor.spawn_named("task-b", async { 2 });

        let info = executor.task_by_name("task-a").unwrap();
        assert_eq!(info.name, Some("task-a".to_string()));

        let info = executor.task_by_name("task-b").unwrap();
        assert_eq!(info.name, Some("task-b".to_string()));

        assert!(executor.task_by_name("nonexistent").is_none());
    }

    #[test]
    fn test_completed_count() {
        let executor = TestExecutor::new();
        executor.spawn(async { 1 });
        executor.spawn(async { 2 });
        executor.spawn(async { 3 });

        assert_eq!(executor.completed_count(), 0);

        let _ = executor.step();
        assert_eq!(executor.completed_count(), 1);

        let _ = executor.run_until_stalled();
        assert_eq!(executor.completed_count(), 3);
    }

    // ========================================================================
    // Deterministic Ordering Tests (Issue #11)
    // ========================================================================

    #[test]
    fn test_fifo_policy() {
        let executor = TestExecutor::with_policy(SchedulingPolicy::Fifo);

        let handle1 = executor.spawn(async { 1 });
        let handle2 = executor.spawn(async { 2 });
        let handle3 = executor.spawn(async { 3 });

        // FIFO: first spawned runs first
        let _ = executor.step();
        assert!(handle1.is_complete());
        assert!(!handle2.is_complete());
        assert!(!handle3.is_complete());

        let _ = executor.step();
        assert!(handle2.is_complete());

        let _ = executor.step();
        assert!(handle3.is_complete());
    }

    #[test]
    fn test_lifo_policy() {
        let executor = TestExecutor::with_policy(SchedulingPolicy::Lifo);

        let handle1 = executor.spawn(async { 1 });
        let handle2 = executor.spawn(async { 2 });
        let handle3 = executor.spawn(async { 3 });

        // LIFO: last spawned runs first
        let _ = executor.step();
        assert!(!handle1.is_complete());
        assert!(!handle2.is_complete());
        assert!(handle3.is_complete());

        let _ = executor.step();
        assert!(handle2.is_complete());

        let _ = executor.step();
        assert!(handle1.is_complete());
    }

    #[test]
    fn test_seeded_random_policy_reproducible() {
        // Same seed should produce same order
        let results1 = {
            let executor = TestExecutor::with_policy(SchedulingPolicy::SeededRandom(42));
            let handles: Vec<_> = (0..10).map(|i| executor.spawn(async move { i })).collect();

            let mut order = Vec::new();
            while executor.pending_count() > 0 {
                let _ = executor.step();
                for (i, h) in handles.iter().enumerate() {
                    if h.is_complete() && !order.contains(&i) {
                        order.push(i);
                    }
                }
            }
            order
        };

        let results2 = {
            let executor = TestExecutor::with_policy(SchedulingPolicy::SeededRandom(42));
            let handles: Vec<_> = (0..10).map(|i| executor.spawn(async move { i })).collect();

            let mut order = Vec::new();
            while executor.pending_count() > 0 {
                let _ = executor.step();
                for (i, h) in handles.iter().enumerate() {
                    if h.is_complete() && !order.contains(&i) {
                        order.push(i);
                    }
                }
            }
            order
        };

        // Same seed produces same execution order
        assert_eq!(results1, results2);
    }

    #[test]
    fn test_seeded_random_different_seeds() {
        // Different seeds should (likely) produce different orders
        let results1 = {
            let executor = TestExecutor::with_policy(SchedulingPolicy::SeededRandom(42));
            let handles: Vec<_> = (0..10).map(|i| executor.spawn(async move { i })).collect();

            let mut order = Vec::new();
            while executor.pending_count() > 0 {
                let _ = executor.step();
                for (i, h) in handles.iter().enumerate() {
                    if h.is_complete() && !order.contains(&i) {
                        order.push(i);
                    }
                }
            }
            order
        };

        let results2 = {
            let executor = TestExecutor::with_policy(SchedulingPolicy::SeededRandom(12345));
            let handles: Vec<_> = (0..10).map(|i| executor.spawn(async move { i })).collect();

            let mut order = Vec::new();
            while executor.pending_count() > 0 {
                let _ = executor.step();
                for (i, h) in handles.iter().enumerate() {
                    if h.is_complete() && !order.contains(&i) {
                        order.push(i);
                    }
                }
            }
            order
        };

        // Different seeds produce different execution orders
        assert_ne!(results1, results2);
    }

    #[test]
    fn test_policy_getter() {
        let executor = TestExecutor::new();
        assert!(matches!(executor.policy(), SchedulingPolicy::Fifo));

        let executor = TestExecutor::with_policy(SchedulingPolicy::Lifo);
        assert!(matches!(executor.policy(), SchedulingPolicy::Lifo));

        let executor = TestExecutor::with_policy(SchedulingPolicy::SeededRandom(42));
        assert!(matches!(
            executor.policy(),
            SchedulingPolicy::SeededRandom(42)
        ));
    }

    #[test]
    fn test_seed_getter() {
        let executor = TestExecutor::with_policy(SchedulingPolicy::SeededRandom(12345));
        assert_eq!(executor.seed(), 12345);
    }
}
