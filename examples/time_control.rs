//! Example: Time control in async tests
//!
//! This example demonstrates how to use `MockClock` to control time in async tests,
//! making tests that involve timeouts, delays, and retries run instantly.

use std::time::Duration;
use testkit_async::clock::MockClock;

fn main() {
    println!("🧰 testkit-async - Time Control Examples\n");

    example_basic_time_control();
    example_time_tracking();
    example_pause_resume();
    example_relative_time();

    println!("\n✅ All time control examples completed!");
}

/// Basic time advancement without waiting
fn example_basic_time_control() {
    println!("📌 Example 1: Basic Time Control");
    println!("   Advancing virtual time without real delays\n");

    let clock = MockClock::new();
    println!("   Initial time: {:?}", clock.now());

    // Advance time by 10 seconds - happens instantly!
    clock.advance(Duration::from_secs(10));
    println!("   After advancing 10s: {:?}", clock.now());

    // Advance by 1 minute
    clock.advance(Duration::from_secs(60));
    println!("   After advancing 60s more: {:?}", clock.now());

    // Advance to a specific time
    clock.advance_to(Duration::from_secs(300));
    println!("   After advancing to 300s: {:?}", clock.now());

    println!("   ⚡ All time changes happened instantly!\n");
}

/// Tracking elapsed time
fn example_time_tracking() {
    println!("📌 Example 2: Time Tracking");
    println!("   Measure elapsed virtual time\n");

    let clock = MockClock::new();

    let start_time = clock.now();
    println!("   Operation started at: {:?}", start_time);

    // Simulate operation taking 5 seconds
    clock.advance(Duration::from_secs(5));
    println!("   After first step: {:?}", clock.now());

    // Simulate additional 3 seconds
    clock.advance(Duration::from_secs(3));
    println!("   After second step: {:?}", clock.now());

    let elapsed = clock.elapsed();
    println!("   Total elapsed time: {:?}", elapsed);

    assert_eq!(elapsed, Duration::from_secs(8));
    println!("   ✓ Verified 8 seconds elapsed!\n");
}

/// Pausing and resuming time
fn example_pause_resume() {
    println!("📌 Example 3: Pause and Resume");
    println!("   Control when time flows\n");

    let clock = MockClock::new();

    println!("   Time is flowing normally");
    clock.advance(Duration::from_secs(5));
    println!("   Current time: {:?}", clock.now());

    // Pause time
    clock.pause();
    println!("\n   ⏸  Time paused! (is_paused: {})", clock.is_paused());
    println!("   Current time while paused: {:?}", clock.now());

    // Note: Cannot advance time while paused!
    // clock.advance() would panic here

    // Resume time
    clock.resume();
    println!("\n   ▶️  Time resumed! (is_paused: {})", clock.is_paused());
    clock.advance(Duration::from_secs(10));
    println!("   After advancing 10s: {:?}", clock.now());
    println!();
}

/// Working with relative time
fn example_relative_time() {
    println!("📌 Example 4: Relative Time");
    println!("   Using cloned clocks and shared time state\n");

    let clock1 = MockClock::new();
    let clock2 = clock1.clone();

    println!("   Clock 1 time: {:?}", clock1.now());
    println!("   Clock 2 time: {:?}", clock2.now());

    // Advance clock1 - both clocks see the change
    println!("\n   Advancing clock1 by 30 seconds...");
    clock1.advance(Duration::from_secs(30));
    println!("   Clock 1 time: {:?}", clock1.now());
    println!("   Clock 2 time: {:?}", clock2.now());

    // They share the same time state!
    assert_eq!(clock1.now(), clock2.now());

    println!("\n   Advancing clock2 by 15 seconds...");
    clock2.advance(Duration::from_secs(15));
    println!("   Clock 1 time: {:?}", clock1.now());
    println!("   Clock 2 time: {:?}", clock2.now());

    println!("\n   ✓ Both clocks share the same virtual time!");
    println!();
}
