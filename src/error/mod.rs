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

    /// Resource exhausted
    #[error("Resource exhausted: {0}")]
    ResourceExhausted(String),

    /// Network error
    #[error("Network error: {0}")]
    Network(String),

    /// Injected failure
    #[error("Injected failure: {0}")]
    InjectedFailure(String),
}

impl Error {
    /// Create a resource exhausted error.
    #[must_use]
    pub fn resource_exhausted(message: impl Into<String>) -> Self {
        Self::ResourceExhausted(message.into())
    }

    /// Create a network error.
    #[must_use]
    pub fn network(message: impl Into<String>) -> Self {
        Self::Network(message.into())
    }

    /// Create an injected failure error.
    #[must_use]
    pub fn injected_failure(message: impl Into<String>) -> Self {
        Self::InjectedFailure(message.into())
    }
}

/// Result type alias
pub type Result<T> = std::result::Result<T, Error>;
