//! # testkit-async 🧰
//!
//! > Practical testing tools for async Rust
//!
//! **testkit-async** provides time control, deterministic execution, and failure
//! injection to make async testing fast, reliable, and easy.
//!
//! ## Quick Start
//!
//! ```rust,ignore
//! use testkit_async::prelude::*;
//!
//! #[testkit_async::test]
//! async fn test_with_timeout() {
//!     let clock = MockClock::new();
//!     
//!     let future = timeout(Duration::from_secs(30), operation());
//!     clock.advance(Duration::from_secs(31));
//!     
//!     assert!(future.await.is_err()); // Instant test!
//! }
//! ```
//!
//! ## Features
//!
//! - ⏱️ **Mock Clock** - Control time without waiting
//! - 🎮 **Deterministic Executor** - Control task execution order
//! - 💥 **Failure Injection** - Simulate errors and timeouts
//! - 🔍 **Async Assertions** - Fluent testing API
//! - 🎯 **Sync Points** - Coordinate multiple tasks

#![warn(missing_docs)]
#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![allow(clippy::module_name_repetitions)]

/// Mock clock for time control in tests
pub mod clock;

pub mod assertions;
pub mod chaos;
pub mod error;
pub mod executor;
pub mod mock;
pub mod sync;

/// Prelude for convenient imports
///
/// ```rust
/// use testkit_async::prelude::*;
/// ```
pub mod prelude {
    pub use crate::clock::*;
    pub use crate::error::{Error, Result};
    pub use crate::executor::{
        SchedulingPolicy, SyncPointFuture, TaskHandle, TaskId, TaskInfo, TaskState, TestExecutor,
    };
}

// Re-exports
pub use error::{Error, Result};

// Re-export the test macro when macros feature is enabled
#[cfg(feature = "macros")]
pub use testkit_async_macros::test;

#[cfg(test)]
mod tests {
    #[test]
    fn test_placeholder() {
        // Placeholder test
        assert_eq!(2 + 2, 4);
    }
}
