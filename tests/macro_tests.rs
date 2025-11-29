//! Integration tests for the `#[testkit_async::test]` macro.

#![cfg(feature = "macros")]
// MockClock is used in function signatures but injected by the macro
#![allow(unused_imports)]

use std::time::Duration;
use testkit_async::clock::MockClock;

/// Basic test without clock injection.
#[testkit_async::test]
async fn test_basic_async() {
    assert_eq!(2 + 2, 4);
}

/// Test with MockClock injection.
#[testkit_async::test]
async fn test_with_clock(clock: MockClock) {
    assert_eq!(clock.now(), Duration::ZERO);

    clock.advance(Duration::from_secs(10));
    assert_eq!(clock.now(), Duration::from_secs(10));
}

/// Test with start_paused configuration.
#[testkit_async::test(start_paused = true)]
async fn test_start_paused(clock: MockClock) {
    assert!(clock.is_paused());
    clock.resume();
    assert!(!clock.is_paused());
}

/// Test with custom start time.
#[testkit_async::test(start_time = 1000)]
async fn test_start_time(clock: MockClock) {
    assert_eq!(clock.now(), Duration::from_secs(1000));
}

/// Test sleep completes when time advances.
#[testkit_async::test]
async fn test_sleep_with_clock(clock: MockClock) {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    let completed = Arc::new(AtomicBool::new(false));
    let completed2 = completed.clone();
    let clock2 = clock.clone();

    let handle = tokio::spawn(async move {
        clock2.sleep(Duration::from_secs(60)).await;
        completed2.store(true, Ordering::SeqCst);
    });

    // Give the task a chance to start
    tokio::task::yield_now().await;

    // Sleep hasn't completed yet
    assert!(!completed.load(Ordering::SeqCst));

    // Advance time past the deadline
    clock.advance(Duration::from_secs(60));

    // Wait for the task to complete
    handle.await.unwrap();

    // Sleep completed!
    assert!(completed.load(Ordering::SeqCst));
}

/// Test with multi_thread flavor.
#[testkit_async::test(flavor = "multi_thread")]
async fn test_multi_thread() {
    let handle = tokio::spawn(async { 42 });
    assert_eq!(handle.await.unwrap(), 42);
}

/// Test with multiple configuration options.
#[testkit_async::test(start_time = 500, start_paused = true)]
async fn test_combined_config(clock: MockClock) {
    assert_eq!(clock.now(), Duration::from_secs(500));
    assert!(clock.is_paused());
}
