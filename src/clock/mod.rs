//! Virtual time control for async tests
//!
//! The `clock` module provides [`MockClock`](crate::clock::MockClock), a virtual clock that allows you to
//! control time in your async tests without waiting for real time to pass.
//!
//! # Example
//!
//! ```rust
//! use testkit_async::clock::MockClock;
//! use std::time::Duration;
//!
//! let clock = MockClock::new();
//! assert_eq!(clock.now(), Duration::ZERO);
//!
//! clock.advance(Duration::from_secs(10));
//! assert_eq!(clock.now(), Duration::from_secs(10));
//! ```

mod mock_clock;
mod sleep;

pub use mock_clock::MockClock;
pub use sleep::{MockDelay, MockSleep};
