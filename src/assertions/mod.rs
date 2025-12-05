//! Fluent assertions for async code.
//!
//! This module provides assertion utilities for async testing:
//!
//! - [`assert_stream`] - Fluent assertions for streams
//! - [`assert_ready!`] - Assert a future is immediately ready
//! - [`assert_pending!`] - Assert a future is not ready
//! - [`poll_once`] - Poll a future once and return the result
//! - [`PollCounter`] - Count how many times a future is polled
//! - [`matcher`] - Custom matcher system for flexible assertions
//!
//! # Stream Assertions
//!
//! ```rust,ignore
//! use testkit_async::assertions::assert_stream;
//! use futures::stream;
//!
//! let s = stream::iter(vec![1, 2, 3]);
//! assert_stream(s)
//!     .next_eq(1).await
//!     .next_eq(2).await
//!     .ends().await;
//! ```
//!
//! # Future Assertions
//!
//! ```rust
//! use testkit_async::{assert_ready, assert_pending};
//! use std::future::ready;
//!
//! // Assert a future is ready
//! let value = assert_ready!(ready(42));
//! assert_eq!(value, 42);
//!
//! // Assert a future is pending
//! assert_pending!(futures::future::pending::<i32>());
//! ```
//!
//! # Custom Matchers
//!
//! ```rust
//! use testkit_async::{assert_that, assertions::matcher::{eq, gt, all_of}};
//!
//! assert_that!(42, eq(42));
//! assert_that!(50, all_of(vec![gt(0), gt(10)]));
//! ```

mod future;
pub mod matcher;
mod stream;

pub use future::{
    poll_once, ready_after_polls, FuturePollResult, PollCountHandle, PollCounter, ReadyAfterPolls,
};
pub use stream::{
    assert_stream, AllMatchFuture, AnyMatchFuture, CollectEqFuture, EndsFuture, HasLengthFuture,
    NextEqFuture, NextMatchesFuture, SkipFuture, StreamAssertion,
};
