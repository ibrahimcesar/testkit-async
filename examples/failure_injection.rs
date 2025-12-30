//! Example: Failure injection and chaos engineering
//!
//! This example demonstrates how to use testkit-async's chaos engineering tools
//! to test how your code handles failures, network issues, and resource exhaustion.

use std::time::Duration;
use testkit_async::chaos::{
    CountingInjector, FailureInjector, LatencyInjector, NetworkSimulator, ProbabilisticInjector,
    ResourceLimiter,
};

fn main() {
    println!("🧰 testkit-async - Failure Injection Examples\n");

    example_counting_injector();
    example_probabilistic_failures();
    example_network_simulation();
    example_latency_injection();
    example_resource_limits();

    println!("\n✅ All chaos engineering examples completed!");
}

/// Using CountingInjector to test retry logic
fn example_counting_injector() {
    println!("📌 Example 1: Counting Injector - Testing Retry Logic");
    println!("   Fail the first N attempts, then succeed\n");

    // Create an injector that fails the first 3 attempts
    let injector = CountingInjector::fail_first(3);

    println!("   Simulating retry logic with 3 initial failures...");
    for i in 0..5 {
        if injector.should_fail() {
            println!("   Attempt {}: ❌ Failed!", i + 1);
        } else {
            println!("   Attempt {}: ✅ Success!", i + 1);
        }
        injector.record_attempt();
    }

    let stats = injector.stats();
    println!("\n   📊 Statistics:");
    println!("      Total attempts: {}", stats.attempts);
    println!("      Failures: {}", stats.failures);
    println!("      Successes: {}", stats.successes);

    // Test "fail every Nth" pattern
    println!("\n   Testing 'fail every 3rd attempt' pattern...");
    let injector = CountingInjector::fail_every(3);

    for i in 0..7 {
        if injector.should_fail() {
            println!("   Attempt {}: ❌ Failed!", i + 1);
        } else {
            println!("   Attempt {}: ✅ Success!", i + 1);
        }
        injector.record_attempt();
    }

    println!();
}

/// Using ProbabilisticInjector for flaky operations
fn example_probabilistic_failures() {
    println!("📌 Example 2: Probabilistic Injector - Simulating Flaky Services");
    println!("   Random failures with controlled probability\n");

    // Create an injector with 30% failure rate (seeded for reproducibility)
    let injector = ProbabilisticInjector::with_seed(0.3, 42);

    println!("   Simulating 20 requests with 30% failure rate...");
    let mut consecutive_failures = 0;
    let mut max_consecutive = 0;

    for i in 0..20 {
        if injector.should_fail() {
            consecutive_failures += 1;
            max_consecutive = max_consecutive.max(consecutive_failures);
            print!("❌");
        } else {
            consecutive_failures = 0;
            print!("✅");
        }
        injector.record_attempt();

        if (i + 1) % 10 == 0 {
            println!();
        }
    }

    let stats = injector.stats();
    println!("\n\n   📊 Statistics:");
    println!("      Total requests: {}", stats.attempts);
    println!("      Failures: {} ({:.1}%)", stats.failures, (stats.failures as f64 / stats.attempts as f64) * 100.0);
    println!("      Successes: {}", stats.successes);
    println!("      Max consecutive failures: {}", max_consecutive);
    println!();
}

/// Simulating network failures
fn example_network_simulation() {
    println!("📌 Example 3: Network Simulator - Testing Network Resilience");
    println!("   Simulate packet loss and connection issues\n");

    let simulator = NetworkSimulator::new();

    // Simulate packet loss
    println!("   Scenario 1: Packet Loss (20% loss rate)");
    simulator.set_loss_rate(0.2);

    let mut lost = 0;
    for i in 0..10 {
        if simulator.should_drop() {
            println!("   Packet {}: 📦❌ Dropped", i + 1);
            lost += 1;
        } else {
            println!("   Packet {}: 📦✅ Delivered", i + 1);
        }
        simulator.record_send();
    }
    println!("   Total packets lost: {}/10", lost);

    // Connection state
    println!("\n   Scenario 2: Connection State");
    println!("   Connection status: {}", if simulator.is_connected() { "✅ Connected" } else { "❌ Disconnected" });

    simulator.disconnect();
    println!("   After disconnect: {}", if simulator.is_connected() { "✅ Connected" } else { "❌ Disconnected" });

    simulator.reconnect();
    println!("   After reconnect: {}", if simulator.is_connected() { "✅ Connected" } else { "❌ Disconnected" });

    // Statistics
    let stats = simulator.stats();
    println!("\n   📊 Network Statistics:");
    println!("      Total sent: {}", stats.messages_sent);
    println!("      Dropped: {}", stats.messages_dropped);
    println!("      Corrupted: {}", stats.messages_corrupted);

    println!();
}

/// Testing with artificial latency
fn example_latency_injection() {
    println!("📌 Example 4: Latency Injector - Testing Performance Under Load");
    println!("   Add artificial delays to test timeout handling\n");

    let clock = testkit_async::clock::MockClock::new();

    // Fixed latency
    println!("   Fixed latency (100ms per request):");
    let latency = LatencyInjector::fixed(Duration::from_millis(100));

    for i in 0..3 {
        let delay = latency.next_delay();
        clock.advance(delay);
        println!("   Request {}: {:?}", i + 1, delay);
    }

    // Uniform latency with jitter
    println!("\n   Uniform latency (50ms-150ms):");
    let latency = LatencyInjector::uniform(
        Duration::from_millis(50),
        Duration::from_millis(150),
    ).with_seed(42); // Seeded for reproducibility

    let total_start = clock.now();
    for i in 0..5 {
        let start = clock.now();
        let delay = latency.next_delay();

        // Simulate the latency
        clock.advance(delay);

        let elapsed = clock.now() - start;
        println!("   Request {}: took {:?}", i + 1, elapsed);
    }

    let total_time = clock.now() - total_start;
    println!("\n   Total time: {:?}", total_time);
    println!("   Average latency: {:?}", total_time / 5);
    println!();
}

/// Testing resource exhaustion scenarios
fn example_resource_limits() {
    println!("📌 Example 5: Resource Limiter - Testing Resource Exhaustion");
    println!("   Simulate connection pools, rate limits, and resource constraints\n");

    // Create a limiter with 3 available connections
    let limiter = ResourceLimiter::new().with_connection_limit(3);

    let status = limiter.status();
    println!("   Simulating a connection pool with {} connections:", status.connection_limit);
    println!("   Available: {}/{}\n", status.connections_available, status.connection_limit);

    // Acquire resources
    println!("   Acquiring resources...");
    let _guard1 = limiter.acquire_connection().unwrap();
    let status = limiter.status();
    println!("   ✅ Acquired connection 1 (available: {}/{})", status.connections_available, status.connection_limit);

    let _guard2 = limiter.acquire_connection().unwrap();
    let status = limiter.status();
    println!("   ✅ Acquired connection 2 (available: {}/{})", status.connections_available, status.connection_limit);

    let guard3 = limiter.acquire_connection().unwrap();
    let status = limiter.status();
    println!("   ✅ Acquired connection 3 (available: {}/{})", status.connections_available, status.connection_limit);

    // Try to acquire when exhausted
    println!("\n   Trying to acquire when pool is exhausted...");
    match limiter.acquire_connection() {
        Ok(_) => println!("   ✅ Acquired (unexpected!)"),
        Err(_) => println!("   ❌ Pool exhausted! (expected)"),
    }

    // Release a resource
    println!("\n   Releasing connection 3...");
    drop(guard3);
    let status = limiter.status();
    println!("   Available: {}/{}", status.connections_available, status.connection_limit);

    // Now we can acquire again
    let _guard4 = limiter.acquire_connection().unwrap();
    let status = limiter.status();
    println!("   ✅ Acquired new connection (available: {}/{})", status.connections_available, status.connection_limit);

    // Statistics
    let stats = limiter.stats();
    println!("\n   📊 Resource Pool Statistics:");
    println!("      Total connection attempts: {}", stats.connection_attempts);
    println!("      Connection exhaustions: {}", stats.connection_exhaustions);
    println!("      Peak connections: {}", stats.peak_connections);

    // Memory allocation example
    println!("\n   Testing memory allocation limits...");
    let mem_limiter = ResourceLimiter::new().with_memory_limit(1000); // 1000 bytes limit

    match mem_limiter.allocate(500) {
        Ok(_guard) => println!("   ✅ Allocated 500 bytes"),
        Err(e) => println!("   ❌ Allocation failed: {}", e),
    }

    match mem_limiter.allocate(600) {
        Ok(_guard) => println!("   ✅ Allocated 600 bytes (unexpected!)"),
        Err(e) => println!("   ❌ Allocation failed (expected): {} bytes would exceed limit", e),
    }

    println!();
}
