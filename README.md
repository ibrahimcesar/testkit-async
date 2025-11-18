<div align="center">

# testkit-async 🧰

_Practical testing tools for async Rust_

**testkit-async** is a comprehensive testing toolkit for async Rust code. It provides time control, deterministic execution, failure injection, and rich assertions to make async testing fast, reliable, and easy.

</div>

## 🎯 Why testkit-async?

### The Problem

Testing async code in Rust is frustrating:
```rust
#[tokio::test]
async fn test_retry_with_timeout() {
    // This test takes 30+ seconds to run! 😱
    let result = retry_with_timeout(
        failing_operation,
        Duration::from_secs(30)
    ).await;
    
    // How do I know retry happened 3 times?
    // How do I test timeout without waiting 30s?
    // How do I make this deterministic?
}
```

**Common issues:**
- ❌ Tests are **slow** (waiting for real time)
- ❌ Tests are **flaky** (race conditions, timing issues)
- ❌ Tests are **hard to write** (complex async coordination)
- ❌ Tests are **unpredictable** (non-deterministic execution)

### The Solution
```rust
use testkit_async::prelude::*;

#[testkit_async::test]
async fn test_retry_with_timeout() {
    let clock = MockClock::new();
    let counter = AtomicU32::new(0);
    
    // Test runs instantly! ⚡
    let future = retry_with_timeout(
        || async { 
            counter.fetch_add(1, Ordering::SeqCst);
            Err("fail") 
        },
        Duration::from_secs(30)
    );
    
    // Advance virtual time - no real waiting!
    clock.advance(Duration::from_secs(31));
    
    // Verify behavior
    assert!(future.await.is_err());
    assert_eq!(counter.load(Ordering::SeqCst), 3); // Retried 3 times!
}
```

## ✨ Features (Planned)

- ⏱️ **Mock Clock** - Control time without waiting
- 🎮 **Deterministic Executor** - Control task execution order
- 💥 **Failure Injection** - Simulate errors, timeouts, network issues
- 🔍 **Async Assertions** - Fluent API for testing streams and futures
- 🎯 **Sync Points** - Coordinate multiple tasks precisely
- 📊 **Test Utilities** - Mocks, spies, and test helpers

## 🚧 Status

**Work in Progress** - Early development

Current version: `0.1.0-alpha`

## 🆚 Comparison with Existing Tools

### What Already Exists

| Tool | What It Does | What's Missing |
|------|--------------|----------------|
| [async-test](https://crates.io/crates/async-test) | Attribute macro for async tests | ❌ No time control<br>❌ No execution control<br>❌ Just a macro wrapper |
| [tokio-test](https://crates.io/crates/tokio-test) | Tokio testing utilities | ⚠️ Tokio-specific only<br>❌ Limited time control<br>❌ No failure injection |
| [futures-test](https://crates.io/crates/futures-test) | Futures test utilities | ❌ No mock clock<br>❌ Low-level only<br>❌ Not ergonomic |
| [mockall](https://crates.io/crates/mockall) | General mocking | ❌ Not async-aware<br>❌ Verbose for async |

### What testkit-async Provides

| Feature | testkit-async | tokio-test | futures-test | async-test |
|---------|---------------|------------|--------------|------------|
| **Mock Clock** | ✅ Full control | ⚠️ Limited | ❌ | ❌ |
| **Deterministic Execution** | ✅ | ❌ | ❌ | ❌ |
| **Failure Injection** | ✅ | ❌ | ❌ | ❌ |
| **Async Assertions** | ✅ | ❌ | ❌ | ❌ |
| **Sync Points** | ✅ | ❌ | ❌ | ❌ |
| **Runtime Agnostic** | ✅ | ❌ Tokio only | ✅ | ✅ |
| **Ergonomic API** | ✅ | ⚠️ | ❌ | ⚠️ |

**Key Differentiators:**
1. **Complete Time Control** - Not just pause/resume, but full virtual time
2. **Deterministic Testing** - Control exact execution order of tasks
3. **Chaos Engineering** - Built-in failure injection and network simulation
4. **High-Level API** - Ergonomic, not low-level primitives

## 📚 Quick Examples (Planned API)

### Time Control
```rust
use testkit_async::prelude::*;

#[testkit_async::test]
async fn test_with_timeout() {
    let clock = MockClock::new();
    
    // This completes instantly in tests!
    let future = timeout(Duration::from_secs(30), slow_operation());
    
    // Advance virtual time
    clock.advance(Duration::from_secs(31));
    
    // Timeout triggered without waiting 30s
    assert!(future.await.is_err());
}
```

### Controlled Concurrency
```rust
use testkit_async::prelude::*;

#[testkit_async::test]
async fn test_race_condition() {
    let executor = TestExecutor::new();
    let counter = Arc::new(Mutex::new(0));
    
    // Spawn two tasks
    let c1 = counter.clone();
    executor.spawn(async move {
        sync_point("before").await;
        *c1.lock().await += 1;
    });
    
    let c2 = counter.clone();
    executor.spawn(async move {
        sync_point("before").await;
        *c2.lock().await += 1;
    });
    
    // Release both simultaneously - guaranteed race!
    executor.release("before");
    executor.run_until_idle().await;
    
    // Now you can test race condition handling
}
```

### Failure Injection
```rust
use testkit_async::chaos::FailureInjector;

#[testkit_async::test]
async fn test_retry_logic() {
    let injector = FailureInjector::new()
        .fail_first(3)  // First 3 calls fail
        .then_succeed();
    
    let client = HttpClient::new()
        .with_interceptor(injector);
    
    let result = retry_request(&client).await?;
    
    // Verify retry worked
    assert_eq!(injector.attempt_count(), 4); // 3 failures + 1 success
    assert!(result.is_ok());
}
```

### Async Assertions
```rust
use testkit_async::prelude::*;

#[testkit_async::test]
async fn test_stream() {
    let stream = create_data_stream();
    
    // Fluent assertions for streams
    assert_stream!(stream)
        .next_eq(1).await
        .next_eq(2).await
        .next_eq(3).await
        .ends().await;
    
    // Timing assertions
    assert_completes_within!(
        Duration::from_millis(100),
        fast_operation()
    ).await;
}
```

### Mock Async Dependencies
```rust
use testkit_async::mock::*;

#[async_trait]
trait DataStore {
    async fn fetch(&self, id: u64) -> Result<Data>;
}

#[testkit_async::test]
async fn test_with_mock() {
    let mut mock = MockDataStore::new();
    
    // Setup expectations
    mock.expect_fetch()
        .with(eq(42))
        .times(1)
        .returning(|_| Ok(Data { value: 100 }));
    
    // Use the mock
    let result = process_data(&mock, 42).await?;
    
    // Verify
    assert_eq!(result.value, 100);
    mock.verify();
}
```

## 🎯 Use Cases

### Fast Test Suites
```rust
// Before: Test suite takes 5 minutes (lots of sleeps/timeouts)
// After: Test suite takes 5 seconds (virtual time)
```

### Deterministic Tests
```rust
// Before: Flaky tests due to race conditions
// After: Deterministic execution, reproducible failures
```

### Chaos Engineering
```rust
// Test resilience to:
// - Network timeouts
// - Random failures
// - Slow responses
// - Connection drops
```

### Integration Testing
```rust
// Test complex async interactions:
// - Multiple services communicating
// - Event-driven systems
// - Stream processing pipelines
```

## 📦 Installation
```bash
# Not yet published - coming soon!
cargo add --dev testkit-async

# Or in Cargo.toml:
[dev-dependencies]
testkit-async = "0.1"
```

## 🗺️ Roadmap

### Phase 1: Time Control (Current)
- [ ] Mock clock implementation
- [ ] Time advancement APIs
- [ ] Integration with tokio::time
- [ ] Pause/resume time

### Phase 2: Execution Control
- [ ] Test executor
- [ ] Sync points
- [ ] Step-by-step execution
- [ ] Task inspection

### Phase 3: Chaos Engineering
- [ ] Failure injector
- [ ] Network simulator
- [ ] Latency injection
- [ ] Resource exhaustion simulation

### Phase 4: Assertions & Utilities
- [ ] Async assertion macros
- [ ] Stream testing helpers
- [ ] Mock trait generation
- [ ] Snapshot testing for async

### Phase 5: Ecosystem Integration
- [ ] Tokio integration
- [ ] async-std integration
- [ ] smol integration
- [ ] Runtime-agnostic core

## 🎨 Design Philosophy

**Ergonomics First:**
- Simple for common cases
- Powerful for complex scenarios
- Minimal boilerplate

**Determinism:**
- Reproducible test results
- No timing-dependent failures
- Controlled execution order

**Fast:**
- Tests run at CPU speed, not wall-clock time
- Parallel-friendly
- Efficient mocking

**Composable:**
- Mix and match features
- Works with existing tools
- Not all-or-nothing

## 🤝 Contributing

Contributions welcome! This project is in early stages.

**Priority areas:**
- [ ] Mock clock implementation
- [ ] Test executor design
- [ ] Failure injection patterns
- [ ] Documentation and examples
- [ ] Runtime compatibility

## 📝 License

MIT OR Apache-2.0

## 🙏 Acknowledgments

Inspired by:
- [tokio-test](https://docs.rs/tokio-test) - Tokio testing utilities
- [futures-test](https://docs.rs/futures-test) - Futures testing primitives
- [async-std](https://async.rs/) - Async runtime ideas
- Testing frameworks from other languages:
  - Python's [pytest-asyncio](https://github.com/pytest-dev/pytest-asyncio)
  - JavaScript's [fake-timers](https://github.com/sinonjs/fake-timers)
  - Go's testing patterns

## 🔗 Related Projects

- [mockall](https://github.com/asomers/mockall) - General mocking (use together!)
- [proptest](https://github.com/proptest-rs/proptest) - Property testing
- [criterion](https://github.com/bheisler/criterion.rs) - Benchmarking

---

**testkit-async** - *Making async testing practical* 🧰

*Status: 🚧 Pre-alpha - Core architecture in design*

**Star** ⭐ this repo to follow development!
