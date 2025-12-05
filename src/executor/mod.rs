//! Controlled async task execution
//!
//! This module provides a [`TestExecutor`] for deterministic async testing.
//! Unlike production executors (tokio, async-std), the `TestExecutor` gives
//! you complete control over when and how tasks execute.
//!
//! # Example
//!
//! ```rust
//! use testkit_async::executor::{TestExecutor, TaskState};
//!
//! let executor = TestExecutor::new();
//!
//! // Spawn tasks - they don't run automatically
//! let handle1 = executor.spawn(async { 1 + 1 });
//! let handle2 = executor.spawn(async { 2 + 2 });
//!
//! assert_eq!(executor.pending_count(), 2);
//!
//! // Step through execution manually
//! executor.step();  // Runs one task
//! executor.step();  // Runs another task
//! ```
//!
//! # Sync Points
//!
//! Use sync points to coordinate multiple tasks:
//!
//! ```rust
//! use testkit_async::executor::TestExecutor;
//!
//! let executor = TestExecutor::new();
//!
//! let sync = executor.sync_point("checkpoint");
//! executor.spawn(async move {
//!     sync.await;
//!     println!("Released!");
//! });
//!
//! executor.run_until_stalled();
//! assert_eq!(executor.waiting_at("checkpoint"), 1);
//!
//! executor.release("checkpoint");
//! executor.run_until_stalled();
//! ```

mod sync_point;
mod task;
mod test_executor;

pub use sync_point::SyncPointFuture;
pub use task::{SchedulingPolicy, TaskHandle, TaskId, TaskInfo, TaskState};
pub use test_executor::TestExecutor;
