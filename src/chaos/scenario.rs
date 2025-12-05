//! Chaos scenario DSL for complex failure patterns.
//!
//! This module provides a domain-specific language for defining complex
//! chaos engineering scenarios.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

use parking_lot::Mutex;

/// A chaos scenario composed of multiple actions.
///
/// Scenarios define a sequence of chaos events that can be triggered
/// based on time, operation count, or probability.
///
/// # Example
///
/// ```rust
/// use std::time::Duration;
/// use testkit_async::chaos::ChaosScenario;
///
/// let scenario = ChaosScenario::builder()
///     .after_ops(5).add_latency(Duration::from_millis(100))
///     .after_ops(10).fail_with_error("connection lost")
///     .build();
///
/// // Check scenario state at different points
/// scenario.record_operation();
/// // ... after 5 operations, latency is added
/// ```
#[derive(Clone)]
pub struct ChaosScenario {
    inner: Arc<ScenarioInner>,
}

struct ScenarioInner {
    actions: Vec<ChaosAction>,
    operation_count: AtomicUsize,
    elapsed: Mutex<Duration>,
    random_state: AtomicUsize,
}

#[derive(Debug)]
struct ChaosAction {
    trigger: ChaosTrigger,
    effect: ChaosEffect,
    fired: std::sync::atomic::AtomicBool,
    repeatable: bool,
}

#[derive(Clone, Debug)]
enum ChaosTrigger {
    /// Trigger after N operations.
    AfterOps(usize),
    /// Trigger at specific elapsed time.
    AtTime(Duration),
    /// Trigger with probability.
    WithProbability(f64),
    // Note: Always variant is intentionally kept for future extensibility
}

#[derive(Clone, Debug)]
enum ChaosEffect {
    /// Add latency to operations.
    AddLatency(Duration),
    /// Fail with an error.
    FailWithError(String),
    /// Disconnect network.
    Disconnect,
    /// Reconnect network.
    Reconnect,
    /// Exhaust connections.
    ExhaustConnections,
    /// Drop next N messages.
    DropMessages(usize),
    /// Corrupt next message.
    CorruptMessage,
    /// Custom effect (for extensibility).
    Custom(String),
}

impl ChaosScenario {
    /// Create a new scenario builder.
    #[must_use]
    pub fn builder() -> ChaosScenarioBuilder {
        ChaosScenarioBuilder::new()
    }

    /// Record that an operation occurred.
    ///
    /// This updates internal counters and may trigger chaos effects.
    pub fn record_operation(&self) {
        self.inner.operation_count.fetch_add(1, Ordering::SeqCst);
    }

    /// Advance the scenario's elapsed time.
    pub fn advance_time(&self, duration: Duration) {
        let mut elapsed = self.inner.elapsed.lock();
        *elapsed += duration;
    }

    /// Get the current operation count.
    #[must_use]
    pub fn operation_count(&self) -> usize {
        self.inner.operation_count.load(Ordering::SeqCst)
    }

    /// Get the current elapsed time.
    #[must_use]
    pub fn elapsed_time(&self) -> Duration {
        *self.inner.elapsed.lock()
    }

    /// Check if any action would add latency now.
    ///
    /// Returns the latency duration if applicable, otherwise `None`.
    #[must_use]
    pub fn check_latency(&self) -> Option<Duration> {
        for action in &self.inner.actions {
            if self.should_trigger(action) {
                if let ChaosEffect::AddLatency(d) = &action.effect {
                    self.mark_fired(action);
                    return Some(*d);
                }
            }
        }
        None
    }

    /// Check if any action would cause a failure now.
    ///
    /// Returns the error message if applicable, otherwise `None`.
    #[must_use]
    pub fn check_failure(&self) -> Option<String> {
        for action in &self.inner.actions {
            if self.should_trigger(action) {
                if let ChaosEffect::FailWithError(msg) = &action.effect {
                    self.mark_fired(action);
                    return Some(msg.clone());
                }
            }
        }
        None
    }

    /// Check if a disconnect should happen now.
    #[must_use]
    pub fn check_disconnect(&self) -> bool {
        for action in &self.inner.actions {
            if self.should_trigger(action) && matches!(action.effect, ChaosEffect::Disconnect) {
                self.mark_fired(action);
                return true;
            }
        }
        false
    }

    /// Check if a reconnect should happen now.
    #[must_use]
    pub fn check_reconnect(&self) -> bool {
        for action in &self.inner.actions {
            if self.should_trigger(action) && matches!(action.effect, ChaosEffect::Reconnect) {
                self.mark_fired(action);
                return true;
            }
        }
        false
    }

    /// Get the current active effect (if any).
    #[must_use]
    pub fn current_effect(&self) -> Option<ScenarioEffect> {
        for action in &self.inner.actions {
            if self.should_trigger(action) {
                self.mark_fired(action);
                return match &action.effect {
                    ChaosEffect::AddLatency(d) => Some(ScenarioEffect::Latency(*d)),
                    ChaosEffect::FailWithError(msg) => Some(ScenarioEffect::Failure(msg.clone())),
                    ChaosEffect::Disconnect => Some(ScenarioEffect::Disconnect),
                    ChaosEffect::Reconnect => Some(ScenarioEffect::Reconnect),
                    ChaosEffect::ExhaustConnections => Some(ScenarioEffect::ExhaustConnections),
                    ChaosEffect::DropMessages(n) => Some(ScenarioEffect::DropMessages(*n)),
                    ChaosEffect::CorruptMessage => Some(ScenarioEffect::CorruptMessage),
                    ChaosEffect::Custom(s) => Some(ScenarioEffect::Custom(s.clone())),
                };
            }
        }
        None
    }

    /// Reset the scenario to its initial state.
    pub fn reset(&self) {
        self.inner.operation_count.store(0, Ordering::SeqCst);
        *self.inner.elapsed.lock() = Duration::ZERO;
        for action in &self.inner.actions {
            action.fired.store(false, Ordering::SeqCst);
        }
    }

    fn should_trigger(&self, action: &ChaosAction) -> bool {
        // Check if already fired (for non-repeatable actions)
        if !action.repeatable && action.fired.load(Ordering::SeqCst) {
            return false;
        }

        match &action.trigger {
            ChaosTrigger::AfterOps(n) => self.operation_count() >= *n,
            ChaosTrigger::AtTime(t) => self.elapsed_time() >= *t,
            ChaosTrigger::WithProbability(p) => {
                let r = self.next_random();
                r < *p
            }
        }
    }

    #[allow(clippy::unused_self)]
    fn mark_fired(&self, action: &ChaosAction) {
        action.fired.store(true, Ordering::SeqCst);
    }

    fn next_random(&self) -> f64 {
        // Simple xorshift for reproducibility
        let mut x = self.inner.random_state.load(Ordering::SeqCst);
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.inner.random_state.store(x, Ordering::SeqCst);
        (x as f64) / (usize::MAX as f64)
    }
}

impl std::fmt::Debug for ChaosScenario {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ChaosScenario")
            .field("operation_count", &self.operation_count())
            .field("elapsed_time", &self.elapsed_time())
            .field("actions", &self.inner.actions)
            .finish()
    }
}

/// Current effect from a scenario.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScenarioEffect {
    /// Add latency.
    Latency(Duration),
    /// Cause a failure.
    Failure(String),
    /// Disconnect network.
    Disconnect,
    /// Reconnect network.
    Reconnect,
    /// Exhaust connections.
    ExhaustConnections,
    /// Drop N messages.
    DropMessages(usize),
    /// Corrupt a message.
    CorruptMessage,
    /// Custom effect.
    Custom(String),
}

/// Builder for creating chaos scenarios.
pub struct ChaosScenarioBuilder {
    actions: Vec<ChaosAction>,
    seed: usize,
}

impl ChaosScenarioBuilder {
    /// Create a new scenario builder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            actions: Vec::new(),
            seed: 0x1234_5678,
        }
    }

    /// Set the random seed for reproducibility.
    #[must_use]
    pub fn with_seed(mut self, seed: usize) -> Self {
        self.seed = seed;
        self
    }

    /// Trigger an action after N operations.
    #[must_use]
    pub fn after_ops(self, count: usize) -> ActionBuilder {
        ActionBuilder {
            builder: self,
            trigger: ChaosTrigger::AfterOps(count),
            repeatable: false,
        }
    }

    /// Trigger an action at a specific time.
    #[must_use]
    pub fn at(self, time: Duration) -> ActionBuilder {
        ActionBuilder {
            builder: self,
            trigger: ChaosTrigger::AtTime(time),
            repeatable: false,
        }
    }

    /// Trigger an action with a probability.
    #[must_use]
    pub fn with_probability(self, p: f64) -> ActionBuilder {
        ActionBuilder {
            builder: self,
            trigger: ChaosTrigger::WithProbability(p),
            repeatable: true, // Probabilistic triggers are usually repeatable
        }
    }

    /// Build the scenario.
    #[must_use]
    pub fn build(self) -> ChaosScenario {
        ChaosScenario {
            inner: Arc::new(ScenarioInner {
                actions: self.actions,
                operation_count: AtomicUsize::new(0),
                elapsed: Mutex::new(Duration::ZERO),
                random_state: AtomicUsize::new(self.seed),
            }),
        }
    }
}

impl Default for ChaosScenarioBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Builder for configuring chaos actions.
pub struct ActionBuilder {
    builder: ChaosScenarioBuilder,
    trigger: ChaosTrigger,
    repeatable: bool,
}

impl ActionBuilder {
    /// Make this action repeatable.
    #[must_use]
    pub fn repeatable(mut self) -> Self {
        self.repeatable = true;
        self
    }

    /// Add latency when triggered.
    #[must_use]
    pub fn add_latency(self, duration: Duration) -> ChaosScenarioBuilder {
        self.add_effect(ChaosEffect::AddLatency(duration))
    }

    /// Fail with an error when triggered.
    #[must_use]
    pub fn fail_with_error(self, message: impl Into<String>) -> ChaosScenarioBuilder {
        self.add_effect(ChaosEffect::FailWithError(message.into()))
    }

    /// Disconnect the network when triggered.
    #[must_use]
    pub fn disconnect(self) -> ChaosScenarioBuilder {
        self.add_effect(ChaosEffect::Disconnect)
    }

    /// Reconnect the network when triggered.
    #[must_use]
    pub fn reconnect(self) -> ChaosScenarioBuilder {
        self.add_effect(ChaosEffect::Reconnect)
    }

    /// Exhaust connections when triggered.
    #[must_use]
    pub fn exhaust_connections(self) -> ChaosScenarioBuilder {
        self.add_effect(ChaosEffect::ExhaustConnections)
    }

    /// Drop N messages when triggered.
    #[must_use]
    pub fn drop_messages(self, count: usize) -> ChaosScenarioBuilder {
        self.add_effect(ChaosEffect::DropMessages(count))
    }

    /// Corrupt the next message when triggered.
    #[must_use]
    pub fn corrupt_message(self) -> ChaosScenarioBuilder {
        self.add_effect(ChaosEffect::CorruptMessage)
    }

    /// Add a custom effect when triggered.
    #[must_use]
    pub fn custom(self, effect: impl Into<String>) -> ChaosScenarioBuilder {
        self.add_effect(ChaosEffect::Custom(effect.into()))
    }

    fn add_effect(mut self, effect: ChaosEffect) -> ChaosScenarioBuilder {
        self.builder.actions.push(ChaosAction {
            trigger: self.trigger,
            effect,
            fired: std::sync::atomic::AtomicBool::new(false),
            repeatable: self.repeatable,
        });
        self.builder
    }
}

/// Pre-built chaos scenarios for common patterns.
pub mod scenarios {
    use super::{ChaosScenario, Duration};

    /// Create a network partition scenario.
    ///
    /// Disconnects at `disconnect_at` and reconnects at `reconnect_at`.
    #[must_use]
    pub fn network_partition(disconnect_at: Duration, reconnect_at: Duration) -> ChaosScenario {
        ChaosScenario::builder()
            .at(disconnect_at)
            .disconnect()
            .at(reconnect_at)
            .reconnect()
            .build()
    }

    /// Create a gradual degradation scenario.
    ///
    /// Latency increases over time.
    #[must_use]
    pub fn gradual_degradation() -> ChaosScenario {
        ChaosScenario::builder()
            .at(Duration::from_secs(5))
            .add_latency(Duration::from_millis(50))
            .at(Duration::from_secs(10))
            .add_latency(Duration::from_millis(100))
            .at(Duration::from_secs(15))
            .add_latency(Duration::from_millis(200))
            .at(Duration::from_secs(20))
            .add_latency(Duration::from_millis(500))
            .build()
    }

    /// Create a random failures scenario.
    ///
    /// Operations have a probability of failing.
    #[must_use]
    pub fn random_failures(failure_probability: f64) -> ChaosScenario {
        ChaosScenario::builder()
            .with_probability(failure_probability)
            .fail_with_error("random failure")
            .build()
    }

    /// Create a scenario where early operations fail.
    ///
    /// The first N operations fail, then everything succeeds.
    #[must_use]
    pub fn fail_first(n: usize) -> ChaosScenario {
        let mut builder = ChaosScenario::builder();
        for i in 0..n {
            builder = builder.after_ops(i).fail_with_error("early failure");
        }
        builder.build()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scenario_after_ops() {
        let scenario = ChaosScenario::builder()
            .after_ops(3)
            .add_latency(Duration::from_millis(100))
            .build();

        // Before 3 ops, no latency
        assert!(scenario.check_latency().is_none());
        scenario.record_operation();
        assert!(scenario.check_latency().is_none());
        scenario.record_operation();
        assert!(scenario.check_latency().is_none());
        scenario.record_operation();

        // After 3 ops, latency triggers
        assert_eq!(scenario.check_latency(), Some(Duration::from_millis(100)));

        // Doesn't trigger again (not repeatable)
        assert!(scenario.check_latency().is_none());
    }

    #[test]
    fn test_scenario_at_time() {
        let scenario = ChaosScenario::builder()
            .at(Duration::from_secs(5))
            .disconnect()
            .build();

        assert!(!scenario.check_disconnect());

        scenario.advance_time(Duration::from_secs(3));
        assert!(!scenario.check_disconnect());

        scenario.advance_time(Duration::from_secs(3)); // Total: 6 secs
        assert!(scenario.check_disconnect());
    }

    #[test]
    fn test_scenario_multiple_actions() {
        let scenario = ChaosScenario::builder()
            .at(Duration::from_secs(5))
            .disconnect()
            .at(Duration::from_secs(10))
            .reconnect()
            .build();

        scenario.advance_time(Duration::from_secs(5));
        assert!(scenario.check_disconnect());
        assert!(!scenario.check_reconnect());

        scenario.advance_time(Duration::from_secs(5));
        assert!(scenario.check_reconnect());
    }

    #[test]
    fn test_scenario_failure() {
        let scenario = ChaosScenario::builder()
            .after_ops(2)
            .fail_with_error("test failure")
            .build();

        scenario.record_operation();
        assert!(scenario.check_failure().is_none());

        scenario.record_operation();
        assert_eq!(scenario.check_failure(), Some("test failure".to_string()));
    }

    #[test]
    fn test_scenario_reset() {
        let scenario = ChaosScenario::builder()
            .after_ops(1)
            .add_latency(Duration::from_millis(100))
            .build();

        scenario.record_operation();
        assert!(scenario.check_latency().is_some());

        scenario.reset();

        assert_eq!(scenario.operation_count(), 0);
        assert!(scenario.check_latency().is_none());
    }

    #[test]
    fn test_current_effect() {
        let scenario = ChaosScenario::builder().after_ops(1).disconnect().build();

        scenario.record_operation();
        assert_eq!(scenario.current_effect(), Some(ScenarioEffect::Disconnect));
    }

    #[test]
    fn test_scenario_clone() {
        let scenario = ChaosScenario::builder()
            .after_ops(5)
            .add_latency(Duration::from_millis(100))
            .build();

        let cloned = scenario.clone();

        for _ in 0..5 {
            scenario.record_operation();
        }

        // Both share state
        assert_eq!(cloned.operation_count(), 5);
    }

    // Pre-built scenarios tests

    #[test]
    fn test_network_partition_scenario() {
        let scenario =
            scenarios::network_partition(Duration::from_secs(5), Duration::from_secs(10));

        scenario.advance_time(Duration::from_secs(5));
        assert!(scenario.check_disconnect());

        scenario.advance_time(Duration::from_secs(5));
        assert!(scenario.check_reconnect());
    }

    #[test]
    fn test_gradual_degradation_scenario() {
        let scenario = scenarios::gradual_degradation();

        scenario.advance_time(Duration::from_secs(5));
        assert_eq!(scenario.check_latency(), Some(Duration::from_millis(50)));

        // Already fired, move to next
        scenario.advance_time(Duration::from_secs(5));
        assert_eq!(scenario.check_latency(), Some(Duration::from_millis(100)));
    }

    #[test]
    fn test_builder_default() {
        let builder = ChaosScenarioBuilder::default();
        let scenario = builder.build();
        assert_eq!(scenario.operation_count(), 0);
    }
}
