//! Network failure simulation.
//!
//! This module provides [`NetworkSimulator`] for simulating network failures,
//! latency, and disconnections.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

use parking_lot::Mutex;

/// Network simulator for testing network failure handling.
///
/// Simulates various network conditions including disconnections,
/// packet loss, and bandwidth limiting.
///
/// # Example
///
/// ```rust
/// use testkit_async::chaos::NetworkSimulator;
///
/// let network = NetworkSimulator::new();
///
/// // Simulate a disconnection
/// network.disconnect();
/// assert!(!network.is_connected());
///
/// // Reconnect
/// network.reconnect();
/// assert!(network.is_connected());
///
/// // Drop the next 3 messages
/// network.drop_next(3);
/// assert!(network.should_drop());
/// assert!(network.should_drop());
/// assert!(network.should_drop());
/// assert!(!network.should_drop()); // 4th message goes through
/// ```
pub struct NetworkSimulator {
    connected: AtomicBool,
    drop_count: AtomicUsize,
    loss_rate: Mutex<f64>,
    bandwidth_bps: AtomicU64,
    corrupt_count: AtomicUsize,
    random_state: AtomicU64,
    stats: Mutex<NetworkStats>,
}

/// Statistics about network simulation.
#[derive(Clone, Copy, Debug, Default)]
pub struct NetworkStats {
    /// Total messages sent.
    pub messages_sent: u64,
    /// Messages dropped.
    pub messages_dropped: u64,
    /// Messages corrupted.
    pub messages_corrupted: u64,
    /// Total disconnection events.
    pub disconnections: u64,
    /// Total reconnection events.
    pub reconnections: u64,
}

impl NetworkSimulator {
    /// Create a new network simulator.
    ///
    /// The network starts in a connected state.
    #[must_use]
    pub fn new() -> Self {
        Self {
            connected: AtomicBool::new(true),
            drop_count: AtomicUsize::new(0),
            loss_rate: Mutex::new(0.0),
            bandwidth_bps: AtomicU64::new(0),
            corrupt_count: AtomicUsize::new(0),
            random_state: AtomicU64::new(0x1234_5678_9ABC_DEF0),
            stats: Mutex::new(NetworkStats::default()),
        }
    }

    /// Create a simulator with a specific random seed.
    #[must_use]
    pub fn with_seed(seed: u64) -> Self {
        Self {
            connected: AtomicBool::new(true),
            drop_count: AtomicUsize::new(0),
            loss_rate: Mutex::new(0.0),
            bandwidth_bps: AtomicU64::new(0),
            corrupt_count: AtomicUsize::new(0),
            random_state: AtomicU64::new(seed),
            stats: Mutex::new(NetworkStats::default()),
        }
    }

    /// Check if the network is currently connected.
    #[must_use]
    pub fn is_connected(&self) -> bool {
        self.connected.load(Ordering::SeqCst)
    }

    /// Simulate a network disconnection.
    ///
    /// All subsequent operations will fail until [`reconnect`] is called.
    ///
    /// [`reconnect`]: NetworkSimulator::reconnect
    pub fn disconnect(&self) {
        self.connected.store(false, Ordering::SeqCst);
        self.stats.lock().disconnections += 1;
    }

    /// Reconnect after a simulated disconnection.
    pub fn reconnect(&self) {
        self.connected.store(true, Ordering::SeqCst);
        self.stats.lock().reconnections += 1;
    }

    /// Drop the next N messages.
    ///
    /// Subsequent calls to [`should_drop`] will return `true` until
    /// N messages have been "dropped".
    ///
    /// [`should_drop`]: NetworkSimulator::should_drop
    pub fn drop_next(&self, count: usize) {
        self.drop_count.fetch_add(count, Ordering::SeqCst);
    }

    /// Set packet loss probability.
    ///
    /// Each message has this probability of being dropped.
    ///
    /// # Panics
    ///
    /// Panics if probability is not in the range [0.0, 1.0].
    pub fn set_loss_rate(&self, probability: f64) {
        assert!(
            (0.0..=1.0).contains(&probability),
            "probability must be between 0.0 and 1.0"
        );
        *self.loss_rate.lock() = probability;
    }

    /// Get the current packet loss rate.
    #[must_use]
    pub fn loss_rate(&self) -> f64 {
        *self.loss_rate.lock()
    }

    /// Set bandwidth limit in bytes per second.
    ///
    /// Use 0 for unlimited bandwidth.
    pub fn set_bandwidth(&self, bytes_per_sec: u64) {
        self.bandwidth_bps.store(bytes_per_sec, Ordering::SeqCst);
    }

    /// Get the current bandwidth limit.
    #[must_use]
    pub fn bandwidth(&self) -> u64 {
        self.bandwidth_bps.load(Ordering::SeqCst)
    }

    /// Mark the next N messages to be corrupted.
    pub fn corrupt_next(&self, count: usize) {
        self.corrupt_count.fetch_add(count, Ordering::SeqCst);
    }

    /// Check if the current message should be dropped.
    ///
    /// Returns `true` if:
    /// - The network is disconnected
    /// - There are pending drops from [`drop_next`]
    /// - Random packet loss based on [`set_loss_rate`]
    ///
    /// This method also updates statistics.
    ///
    /// [`drop_next`]: NetworkSimulator::drop_next
    /// [`set_loss_rate`]: NetworkSimulator::set_loss_rate
    #[must_use]
    pub fn should_drop(&self) -> bool {
        // Check disconnection
        if !self.is_connected() {
            self.stats.lock().messages_dropped += 1;
            return true;
        }

        // Check pending drops
        let drops = self.drop_count.load(Ordering::SeqCst);
        if drops > 0 {
            self.drop_count.fetch_sub(1, Ordering::SeqCst);
            self.stats.lock().messages_dropped += 1;
            return true;
        }

        // Check probabilistic loss
        let loss_rate = *self.loss_rate.lock();
        if loss_rate > 0.0 && self.next_random() < loss_rate {
            self.stats.lock().messages_dropped += 1;
            return true;
        }

        false
    }

    /// Check if the current message should be corrupted.
    ///
    /// Returns `true` if there are pending corruptions from [`corrupt_next`].
    ///
    /// [`corrupt_next`]: NetworkSimulator::corrupt_next
    #[must_use]
    pub fn should_corrupt(&self) -> bool {
        let corrupts = self.corrupt_count.load(Ordering::SeqCst);
        if corrupts > 0 {
            self.corrupt_count.fetch_sub(1, Ordering::SeqCst);
            self.stats.lock().messages_corrupted += 1;
            return true;
        }
        false
    }

    /// Calculate the delay for a message of the given size based on bandwidth.
    ///
    /// Returns `Duration::ZERO` if bandwidth is unlimited.
    #[must_use]
    pub fn transfer_delay(&self, bytes: u64) -> std::time::Duration {
        let bandwidth = self.bandwidth_bps.load(Ordering::SeqCst);
        if bandwidth == 0 {
            return std::time::Duration::ZERO;
        }

        let nanos = (u128::from(bytes) * 1_000_000_000) / u128::from(bandwidth);
        std::time::Duration::from_nanos(nanos as u64)
    }

    /// Record a successful message send.
    pub fn record_send(&self) {
        self.stats.lock().messages_sent += 1;
    }

    /// Get network statistics.
    #[must_use]
    pub fn stats(&self) -> NetworkStats {
        *self.stats.lock()
    }

    /// Reset the simulator to its initial state.
    pub fn reset(&self) {
        self.connected.store(true, Ordering::SeqCst);
        self.drop_count.store(0, Ordering::SeqCst);
        *self.loss_rate.lock() = 0.0;
        self.bandwidth_bps.store(0, Ordering::SeqCst);
        self.corrupt_count.store(0, Ordering::SeqCst);
        *self.stats.lock() = NetworkStats::default();
    }

    fn next_random(&self) -> f64 {
        // xorshift64
        let mut x = self.random_state.load(Ordering::SeqCst);
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.random_state.store(x, Ordering::SeqCst);
        (x as f64) / (u64::MAX as f64)
    }
}

impl Default for NetworkSimulator {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for NetworkSimulator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NetworkSimulator")
            .field("connected", &self.is_connected())
            .field("drop_count", &self.drop_count.load(Ordering::Relaxed))
            .field("loss_rate", &*self.loss_rate.lock())
            .field("bandwidth_bps", &self.bandwidth_bps.load(Ordering::Relaxed))
            .field("stats", &*self.stats.lock())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_simulator_is_connected() {
        let network = NetworkSimulator::new();
        assert!(network.is_connected());
    }

    #[test]
    fn test_disconnect_reconnect() {
        let network = NetworkSimulator::new();

        network.disconnect();
        assert!(!network.is_connected());

        network.reconnect();
        assert!(network.is_connected());

        let stats = network.stats();
        assert_eq!(stats.disconnections, 1);
        assert_eq!(stats.reconnections, 1);
    }

    #[test]
    fn test_drop_next() {
        let network = NetworkSimulator::new();

        network.drop_next(3);

        assert!(network.should_drop());
        assert!(network.should_drop());
        assert!(network.should_drop());
        assert!(!network.should_drop());

        let stats = network.stats();
        assert_eq!(stats.messages_dropped, 3);
    }

    #[test]
    fn test_should_drop_when_disconnected() {
        let network = NetworkSimulator::new();
        network.disconnect();

        assert!(network.should_drop());
        assert!(network.should_drop());

        let stats = network.stats();
        assert_eq!(stats.messages_dropped, 2);
    }

    #[test]
    fn test_loss_rate_zero() {
        let network = NetworkSimulator::new();
        network.set_loss_rate(0.0);

        for _ in 0..100 {
            assert!(!network.should_drop());
        }
    }

    #[test]
    fn test_loss_rate_one() {
        let network = NetworkSimulator::new();
        network.set_loss_rate(1.0);

        for _ in 0..10 {
            assert!(network.should_drop());
        }
    }

    #[test]
    fn test_corrupt_next() {
        let network = NetworkSimulator::new();

        network.corrupt_next(2);

        assert!(network.should_corrupt());
        assert!(network.should_corrupt());
        assert!(!network.should_corrupt());

        let stats = network.stats();
        assert_eq!(stats.messages_corrupted, 2);
    }

    #[test]
    fn test_bandwidth_unlimited() {
        let network = NetworkSimulator::new();
        assert_eq!(network.bandwidth(), 0);
        assert_eq!(network.transfer_delay(1000), std::time::Duration::ZERO);
    }

    #[test]
    fn test_bandwidth_limited() {
        let network = NetworkSimulator::new();
        network.set_bandwidth(1000); // 1000 bytes per second

        // 1000 bytes at 1000 B/s = 1 second
        let delay = network.transfer_delay(1000);
        assert_eq!(delay, std::time::Duration::from_secs(1));

        // 500 bytes at 1000 B/s = 0.5 seconds
        let delay = network.transfer_delay(500);
        assert_eq!(delay, std::time::Duration::from_millis(500));
    }

    #[test]
    fn test_record_send() {
        let network = NetworkSimulator::new();

        network.record_send();
        network.record_send();
        network.record_send();

        assert_eq!(network.stats().messages_sent, 3);
    }

    #[test]
    fn test_reset() {
        let network = NetworkSimulator::new();

        network.disconnect();
        network.drop_next(5);
        network.set_loss_rate(0.5);
        network.set_bandwidth(1000);
        network.corrupt_next(3);
        network.record_send();

        network.reset();

        assert!(network.is_connected());
        assert!(!network.should_drop());
        assert_eq!(network.loss_rate(), 0.0);
        assert_eq!(network.bandwidth(), 0);
        assert!(!network.should_corrupt());
        assert_eq!(network.stats().messages_sent, 0);
    }

    #[test]
    fn test_seeded_reproducible() {
        let results1: Vec<_> = {
            let network = NetworkSimulator::with_seed(42);
            network.set_loss_rate(0.5);
            (0..10).map(|_| network.should_drop()).collect()
        };

        let results2: Vec<_> = {
            let network = NetworkSimulator::with_seed(42);
            network.set_loss_rate(0.5);
            (0..10).map(|_| network.should_drop()).collect()
        };

        assert_eq!(results1, results2);
    }

    #[test]
    #[should_panic(expected = "probability must be between 0.0 and 1.0")]
    fn test_invalid_loss_rate_high() {
        let network = NetworkSimulator::new();
        network.set_loss_rate(1.5);
    }

    #[test]
    #[should_panic(expected = "probability must be between 0.0 and 1.0")]
    fn test_invalid_loss_rate_negative() {
        let network = NetworkSimulator::new();
        network.set_loss_rate(-0.1);
    }

    #[test]
    fn test_default() {
        let network = NetworkSimulator::default();
        assert!(network.is_connected());
    }
}
