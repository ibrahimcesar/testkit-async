//! Error definitions
//!
//! This module provides error types for testkit-async.

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
