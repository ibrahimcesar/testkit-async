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
pub mod clock {
    //! Virtual time control for async tests
}

/// Test executor with deterministic execution
pub mod executor {
    //! Controlled async task execution
}

/// Failure injection and chaos engineering
pub mod chaos {
    //! Simulate failures, timeouts, and errors
}

/// Async assertions and test helpers
pub mod assertions {
    //! Fluent assertions for async code
}

/// Synchronization primitives for tests
pub mod sync {
    //! Sync points and coordination helpers
}

/// Mock trait helpers
pub mod mock {
    //! Utilities for mocking async traits
}

/// Error types
pub mod error {
    //! Error definitions
    
    use thiserror::Error;
    
    /// Main error type for testkit-async
    #[derive(Error, Debug)]
    pub enum Error {
        /// Timeout error
        #[error("Operation timed out after {0:?}")]
        Timeout(std::time::Duration),
        
        /// Assertion failed
        #[error("Assertion failed: {0}")]
        AssertionFailed(String),
        
        /// Mock error
        #[error("Mock error: {0}")]
        Mock(String),
    }
    
    /// Result type alias
    pub type Result<T> = std::result::Result<T, Error>;
}

/// Prelude for convenient imports
pub mod prelude {
    //! Convenient re-exports
    //!
    //! ```rust
    //! use testkit_async::prelude::*;
    //! ```
    
    pub use crate::clock::*;
    pub use crate::executor::*;
    pub use crate::chaos::*;
    pub use crate::assertions::*;
    pub use crate::sync::*;
    pub use crate::error::{Error, Result};
    
    // Re-export macros if available
    #[cfg(feature = "macros")]
    pub use testkit_async_macros::test;
}

// Re-exports
pub use error::{Error, Result};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_placeholder() {
        // Placeholder test
        assert_eq!(2 + 2, 4);
    }
}
