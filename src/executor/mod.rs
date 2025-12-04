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

mod task;
mod test_executor;

pub use task::{TaskHandle, TaskId, TaskInfo, TaskState};
pub use test_executor::TestExecutor;
