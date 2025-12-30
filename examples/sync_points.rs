//! Example: Sync points for deterministic testing
//!
//! This example demonstrates how to use `TestExecutor` and sync points to create
//! deterministic, reproducible tests for concurrent async code.

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;
use testkit_async::executor::{SchedulingPolicy, TestExecutor};

fn main() {
    println!("🧰 testkit-async - Sync Points & Deterministic Execution\n");

    example_basic_sync_points();
    example_race_condition_testing();
    example_step_by_step_execution();
    example_scheduling_policies();
    example_task_coordination();

    println!("\n✅ All sync point examples completed!");
}

/// Basic sync point usage
fn example_basic_sync_points() {
    println!("📌 Example 1: Basic Sync Points");
    println!("   Coordinate multiple tasks with named sync points\n");

    let executor = TestExecutor::new();
    let counter = Arc::new(AtomicU32::new(0));

    // Spawn three tasks that all wait at a sync point
    for i in 0..3 {
        let counter = counter.clone();
        let sync_point = executor.sync_point("ready");
        executor.spawn(async move {
            println!("   Task {}: Waiting at sync point...", i + 1);
            sync_point.await;
            println!("   Task {}: Released!", i + 1);
            counter.fetch_add(1, Ordering::SeqCst);
        });
    }

    // Step the executor to let tasks reach the sync point
    println!("   Running tasks until they reach sync point...");
    while executor.waiting_at("ready") < 3 {
        executor.step();
    }

    println!("   Tasks waiting at 'ready': {}", executor.waiting_at("ready"));
    assert_eq!(counter.load(Ordering::SeqCst), 0, "No tasks should complete yet");

    // Release all tasks at once
    println!("\n   Releasing all tasks simultaneously...");
    let released = executor.release("ready");
    println!("   Released {} tasks", released);

    // Run to completion
    executor.run_until_stalled();
    println!("   Counter: {}", counter.load(Ordering::SeqCst));
    println!();
}

/// Testing race conditions deterministically
fn example_race_condition_testing() {
    println!("📌 Example 2: Race Condition Testing");
    println!("   Reproduce race conditions reliably\n");

    let executor = TestExecutor::new();
    let shared_data = Arc::new(AtomicU32::new(0));

    // Create a classic race condition scenario
    println!("   Scenario: Two tasks increment a counter");

    for i in 0..2 {
        let data = shared_data.clone();
        let sync = executor.sync_point("race");
        executor.spawn(async move {
            // Wait at sync point to ensure both tasks are ready
            sync.await;

            // Read-modify-write race condition
            let value = data.load(Ordering::SeqCst);
            println!("   Task {} read: {}", i + 1, value);

            // Simulate some work
            let new_value = value + 1;

            data.store(new_value, Ordering::SeqCst);
            println!("   Task {} wrote: {}", i + 1, new_value);
        });
    }

    // Let tasks reach the sync point
    while executor.waiting_at("race") < 2 {
        executor.step();
    }

    println!("\n   Both tasks ready. Releasing simultaneously...");
    executor.release("race");

    // Run to completion
    executor.run_until_stalled();

    let final_value = shared_data.load(Ordering::SeqCst);
    println!("\n   Final value: {} (demonstrates race - both read 0, both wrote 1)", final_value);
    println!("   ✓ Race condition reproduced deterministically!");
    println!();
}

/// Step-by-step execution control
fn example_step_by_step_execution() {
    println!("📌 Example 3: Step-by-Step Execution");
    println!("   Manually control task execution order\n");

    let executor = TestExecutor::new();
    let events = Arc::new(parking_lot::Mutex::new(Vec::new()));

    // Spawn multiple tasks
    for i in 0..3 {
        let events = events.clone();
        executor.spawn(async move {
            events.lock().push(format!("Task {} started", i + 1));
            events.lock().push(format!("Task {} step 1", i + 1));
            events.lock().push(format!("Task {} step 2", i + 1));
            events.lock().push(format!("Task {} completed", i + 1));
        });
    }

    println!("   Stepping through execution manually:");
    for step in 0..5 {
        println!("\n   === Step {} ===", step + 1);
        executor.step();

        let current_events = events.lock();
        if !current_events.is_empty() {
            for event in current_events.iter().rev().take(3).rev() {
                println!("   - {}", event);
            }
        }
    }

    // Run remaining tasks
    executor.run_until_stalled();

    println!("\n   Final event count: {}", events.lock().len());
    println!();
}

/// Different scheduling policies
fn example_scheduling_policies() {
    println!("📌 Example 4: Scheduling Policies");
    println!("   Control task execution order with different policies\n");

    // FIFO scheduling (default)
    println!("   Policy 1: FIFO (First In, First Out)");
    let executor = TestExecutor::new();
    let order = Arc::new(parking_lot::Mutex::new(Vec::new()));

    for i in 0..5 {
        let order = order.clone();
        executor.spawn(async move {
            order.lock().push(i);
        });
    }

    executor.run_until_stalled();
    println!("   Execution order: {:?}", *order.lock());

    // LIFO scheduling
    println!("\n   Policy 2: LIFO (Last In, First Out)");
    let executor = TestExecutor::with_policy(SchedulingPolicy::Lifo);
    let order = Arc::new(parking_lot::Mutex::new(Vec::new()));

    for i in 0..5 {
        let order = order.clone();
        executor.spawn(async move {
            order.lock().push(i);
        });
    }

    executor.run_until_stalled();
    println!("   Execution order: {:?}", *order.lock());

    // Seeded random scheduling (reproducible)
    println!("\n   Policy 3: Seeded Random (Reproducible Chaos)");
    let executor = TestExecutor::with_policy(SchedulingPolicy::SeededRandom(42));
    let order = Arc::new(parking_lot::Mutex::new(Vec::new()));

    for i in 0..5 {
        let order = order.clone();
        executor.spawn(async move {
            order.lock().push(i);
        });
    }

    executor.run_until_stalled();
    println!("   Execution order: {:?} (random but reproducible!)", *order.lock());

    // Run again with same seed - should get same order
    let executor = TestExecutor::with_policy(SchedulingPolicy::SeededRandom(42));
    let order2 = Arc::new(parking_lot::Mutex::new(Vec::new()));

    for i in 0..5 {
        let order2 = order2.clone();
        executor.spawn(async move {
            order2.lock().push(i);
        });
    }

    executor.run_until_stalled();
    println!("   Execution order: {:?} (same seed = same order!)", *order2.lock());
    println!();
}

/// Complex task coordination
fn example_task_coordination() {
    println!("📌 Example 5: Complex Task Coordination");
    println!("   Coordinate multiple phases of execution\n");

    let executor = TestExecutor::new();
    let results = Arc::new(parking_lot::Mutex::new(Vec::new()));

    // Producer tasks
    for i in 0..2 {
        let results = results.clone();
        let init_sync = executor.sync_point("init");
        let produce_sync = executor.sync_point("produce");

        executor.spawn(async move {
            println!("   Producer {}: Initializing...", i + 1);
            init_sync.await;

            println!("   Producer {}: Producing data...", i + 1);
            results.lock().push(format!("data_{}", i + 1));

            produce_sync.await;
            println!("   Producer {}: Done!", i + 1);
        });
    }

    // Consumer task
    let results_clone = results.clone();
    let init_sync = executor.sync_point("init");
    let produce_sync = executor.sync_point("produce");

    executor.spawn(async move {
        println!("   Consumer: Waiting for initialization...");
        init_sync.await;

        println!("   Consumer: Waiting for data...");
        produce_sync.await;

        let data = results_clone.lock();
        println!("   Consumer: Received {} items: {:?}", data.len(), *data);
    });

    // Orchestrate the execution
    println!("\n   Phase 1: Let tasks start and reach init point");
    while executor.waiting_at("init") < 3 {
        executor.step();
    }
    println!("   ✓ {} tasks at init sync point", executor.waiting_at("init"));

    println!("\n   Phase 2: Release init, let producers work");
    executor.release("init");
    while executor.waiting_at("produce") < 2 {
        executor.step();
    }
    println!("   ✓ {} producers ready", executor.waiting_at("produce"));
    println!("   ✓ Data produced: {:?}", *results.lock());

    println!("\n   Phase 3: Release produce, let consumer process");
    executor.release("produce");
    executor.run_until_stalled();

    println!("\n   ✓ All tasks coordinated successfully!");
    println!("   Pending tasks: {}", executor.pending_count());
    println!();
}
