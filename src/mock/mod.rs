//! Utilities for mocking async traits and components.
//!
//! This module provides helpers for testing async code:
//!
//! - [`MockChannel`] - Mock channel for testing message passing
//! - [`Spy`] - Function spy for recording calls
//! - [`CallTracker`] - Simple call tracking without wrapping
//!
//! # Mock Channels
//!
//! ```rust
//! use testkit_async::mock::MockChannel;
//!
//! let (tx, rx) = MockChannel::<i32>::unbounded();
//!
//! tx.send(1).unwrap();
//! tx.send(2).unwrap();
//!
//! assert_eq!(tx.sent_messages(), vec![1, 2]);
//! ```
//!
//! # Function Spies
//!
//! ```rust
//! use testkit_async::mock::{Spy, SpyFn};
//!
//! let spy = Spy::new(|x: i32| x * 2);
//! let result = spy.call(5);
//!
//! assert_eq!(result, 10);
//! assert!(spy.was_called());
//! ```

mod channel;
mod spy;

pub use channel::{
    MockChannel, MockReceiver, MockSender, RecvError, RecvFuture, SendError, SendFuture,
    TryRecvError,
};
pub use spy::{AsyncSpy, CallRecord, CallTracker, Spy, SpyFn, TrackedCall};
