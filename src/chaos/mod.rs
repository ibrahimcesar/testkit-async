// Allow certain lints in this module since we're doing low-level numeric operations
#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_precision_loss)]
#![allow(clippy::missing_fields_in_debug)]

//! Simulate failures, timeouts, and chaos engineering scenarios.
//!
//! This module provides tools for testing how your async code handles failures:
//!
//! - [`FailureInjector`] - Core trait for failure injection
//! - [`CountingInjector`] - Fail based on call count (first N, every Nth)
//! - [`ProbabilisticInjector`] - Fail with a probability
//! - [`LatencyInjector`] - Add artificial delays
//! - [`NetworkSimulator`] - Simulate network failures
//! - [`ResourceLimiter`] - Simulate resource exhaustion
//! - [`ChaosScenario`] - Complex multi-stage failure scenarios
//!
//! # Example
//!
//! ```rust
//! use testkit_async::chaos::{FailureInjector, CountingInjector};
//!
//! // Fail the first 3 attempts, then succeed
//! let injector = CountingInjector::fail_first(3);
//!
//! for i in 0..5 {
//!     if injector.should_fail() {
//!         println!("Attempt {} failed!", i);
//!     } else {
//!         println!("Attempt {} succeeded!", i);
//!     }
//!     injector.record_attempt();
//! }
//!
//! // Check statistics
//! let stats = injector.stats();
//! assert_eq!(stats.attempts, 5);
//! assert_eq!(stats.failures, 3);
//! assert_eq!(stats.successes, 2);
//! ```

mod injector;
mod latency;
mod network;
mod resource;
mod scenario;

pub use injector::{
    CountingInjector, FailureInjector, InjectorStats, ProbabilisticInjector, SequenceInjector,
};
pub use latency::LatencyInjector;
pub use network::NetworkSimulator;
pub use resource::{ResourceGuard, ResourceLimiter, ResourceStatus};
pub use scenario::{scenarios, ActionBuilder, ChaosScenario, ChaosScenarioBuilder};
