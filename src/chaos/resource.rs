//! Resource exhaustion simulation.
//!
//! This module provides [`ResourceLimiter`] for simulating resource exhaustion
//! scenarios like memory pressure, connection pool limits, and file descriptor limits.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use parking_lot::Mutex;

use crate::error::Error;

/// Resource limiter for simulating resource exhaustion.
///
/// Simulates limited resources like memory, connections, or file descriptors.
///
/// # Example
///
/// ```rust
/// use testkit_async::chaos::{ResourceLimiter, ResourceGuard};
///
/// let limiter = ResourceLimiter::new()
///     .with_connection_limit(2);
///
/// // Acquire two connections
/// let conn1 = limiter.acquire_connection().unwrap();
/// let conn2 = limiter.acquire_connection().unwrap();
///
/// // Third connection fails - limit reached
/// assert!(limiter.acquire_connection().is_err());
///
/// // Release one
/// drop(conn1);
///
/// // Now we can acquire again
/// let conn3 = limiter.acquire_connection().unwrap();
/// ```
#[derive(Clone)]
pub struct ResourceLimiter {
    inner: Arc<LimiterInner>,
}

struct LimiterInner {
    memory_limit: AtomicUsize,
    memory_used: AtomicUsize,
    connection_limit: AtomicUsize,
    connections_used: AtomicUsize,
    fd_limit: AtomicUsize,
    fds_used: AtomicUsize,
    stats: Mutex<ResourceStats>,
}

/// Current status of resource availability.
#[derive(Clone, Copy, Debug, Default)]
pub struct ResourceStatus {
    /// Memory limit in bytes (0 = unlimited).
    pub memory_limit: usize,
    /// Memory currently in use.
    pub memory_used: usize,
    /// Memory available.
    pub memory_available: usize,
    /// Connection limit (0 = unlimited).
    pub connection_limit: usize,
    /// Connections currently in use.
    pub connections_used: usize,
    /// Connections available.
    pub connections_available: usize,
    /// File descriptor limit (0 = unlimited).
    pub fd_limit: usize,
    /// File descriptors currently in use.
    pub fds_used: usize,
    /// File descriptors available.
    pub fds_available: usize,
}

/// Statistics about resource usage.
#[derive(Clone, Copy, Debug, Default)]
pub struct ResourceStats {
    /// Total memory allocation attempts.
    pub memory_allocations: u64,
    /// Memory allocations that failed due to limits.
    pub memory_exhaustions: u64,
    /// Total connection attempts.
    pub connection_attempts: u64,
    /// Connections that failed due to limits.
    pub connection_exhaustions: u64,
    /// Total file descriptor attempts.
    pub fd_attempts: u64,
    /// File descriptors that failed due to limits.
    pub fd_exhaustions: u64,
    /// Peak memory usage.
    pub peak_memory: usize,
    /// Peak connections.
    pub peak_connections: usize,
}

impl ResourceLimiter {
    /// Create a new resource limiter with no limits.
    #[must_use]
    pub fn new() -> Self {
        Self {
            inner: Arc::new(LimiterInner {
                memory_limit: AtomicUsize::new(0),
                memory_used: AtomicUsize::new(0),
                connection_limit: AtomicUsize::new(0),
                connections_used: AtomicUsize::new(0),
                fd_limit: AtomicUsize::new(0),
                fds_used: AtomicUsize::new(0),
                stats: Mutex::new(ResourceStats::default()),
            }),
        }
    }

    /// Set the memory limit in bytes.
    ///
    /// Use 0 for unlimited.
    #[must_use]
    pub fn with_memory_limit(self, bytes: usize) -> Self {
        self.inner.memory_limit.store(bytes, Ordering::SeqCst);
        self
    }

    /// Set the connection limit.
    ///
    /// Use 0 for unlimited.
    #[must_use]
    pub fn with_connection_limit(self, max: usize) -> Self {
        self.inner.connection_limit.store(max, Ordering::SeqCst);
        self
    }

    /// Set the file descriptor limit.
    ///
    /// Use 0 for unlimited.
    #[must_use]
    pub fn with_fd_limit(self, max: usize) -> Self {
        self.inner.fd_limit.store(max, Ordering::SeqCst);
        self
    }

    /// Get the current resource status.
    #[must_use]
    pub fn status(&self) -> ResourceStatus {
        let memory_limit = self.inner.memory_limit.load(Ordering::SeqCst);
        let memory_used = self.inner.memory_used.load(Ordering::SeqCst);
        let connection_limit = self.inner.connection_limit.load(Ordering::SeqCst);
        let connections_used = self.inner.connections_used.load(Ordering::SeqCst);
        let fd_limit = self.inner.fd_limit.load(Ordering::SeqCst);
        let fds_used = self.inner.fds_used.load(Ordering::SeqCst);

        ResourceStatus {
            memory_limit,
            memory_used,
            memory_available: if memory_limit > 0 {
                memory_limit.saturating_sub(memory_used)
            } else {
                usize::MAX
            },
            connection_limit,
            connections_used,
            connections_available: if connection_limit > 0 {
                connection_limit.saturating_sub(connections_used)
            } else {
                usize::MAX
            },
            fd_limit,
            fds_used,
            fds_available: if fd_limit > 0 {
                fd_limit.saturating_sub(fds_used)
            } else {
                usize::MAX
            },
        }
    }

    /// Attempt to allocate simulated memory.
    ///
    /// Returns a guard that releases the memory when dropped.
    ///
    /// # Errors
    ///
    /// Returns an error if the allocation would exceed the memory limit.
    pub fn allocate(&self, bytes: usize) -> Result<ResourceGuard, Error> {
        self.inner.stats.lock().memory_allocations += 1;

        let limit = self.inner.memory_limit.load(Ordering::SeqCst);
        if limit > 0 {
            let current = self.inner.memory_used.load(Ordering::SeqCst);
            if current + bytes > limit {
                self.inner.stats.lock().memory_exhaustions += 1;
                return Err(Error::resource_exhausted("memory limit exceeded"));
            }
        }

        self.inner.memory_used.fetch_add(bytes, Ordering::SeqCst);

        // Track peak
        let used = self.inner.memory_used.load(Ordering::SeqCst);
        let mut stats = self.inner.stats.lock();
        if used > stats.peak_memory {
            stats.peak_memory = used;
        }

        Ok(ResourceGuard {
            limiter: Arc::clone(&self.inner),
            resource: ResourceType::Memory(bytes),
        })
    }

    /// Attempt to acquire a connection.
    ///
    /// Returns a guard that releases the connection when dropped.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection limit has been reached.
    pub fn acquire_connection(&self) -> Result<ResourceGuard, Error> {
        self.inner.stats.lock().connection_attempts += 1;

        let limit = self.inner.connection_limit.load(Ordering::SeqCst);
        if limit > 0 {
            let current = self.inner.connections_used.load(Ordering::SeqCst);
            if current >= limit {
                self.inner.stats.lock().connection_exhaustions += 1;
                return Err(Error::resource_exhausted("connection limit exceeded"));
            }
        }

        self.inner.connections_used.fetch_add(1, Ordering::SeqCst);

        // Track peak
        let used = self.inner.connections_used.load(Ordering::SeqCst);
        let mut stats = self.inner.stats.lock();
        if used > stats.peak_connections {
            stats.peak_connections = used;
        }

        Ok(ResourceGuard {
            limiter: Arc::clone(&self.inner),
            resource: ResourceType::Connection,
        })
    }

    /// Attempt to acquire a file descriptor.
    ///
    /// Returns a guard that releases the file descriptor when dropped.
    ///
    /// # Errors
    ///
    /// Returns an error if the file descriptor limit has been reached.
    pub fn acquire_fd(&self) -> Result<ResourceGuard, Error> {
        self.inner.stats.lock().fd_attempts += 1;

        let limit = self.inner.fd_limit.load(Ordering::SeqCst);
        if limit > 0 {
            let current = self.inner.fds_used.load(Ordering::SeqCst);
            if current >= limit {
                self.inner.stats.lock().fd_exhaustions += 1;
                return Err(Error::resource_exhausted("file descriptor limit exceeded"));
            }
        }

        self.inner.fds_used.fetch_add(1, Ordering::SeqCst);

        Ok(ResourceGuard {
            limiter: Arc::clone(&self.inner),
            resource: ResourceType::FileDescriptor,
        })
    }

    /// Get resource statistics.
    #[must_use]
    pub fn stats(&self) -> ResourceStats {
        *self.inner.stats.lock()
    }

    /// Reset the limiter to its initial state.
    pub fn reset(&self) {
        self.inner.memory_used.store(0, Ordering::SeqCst);
        self.inner.connections_used.store(0, Ordering::SeqCst);
        self.inner.fds_used.store(0, Ordering::SeqCst);
        *self.inner.stats.lock() = ResourceStats::default();
    }
}

impl Default for ResourceLimiter {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for ResourceLimiter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ResourceLimiter")
            .field("status", &self.status())
            .field("stats", &*self.inner.stats.lock())
            .finish()
    }
}

#[derive(Debug)]
enum ResourceType {
    Memory(usize),
    Connection,
    FileDescriptor,
}

/// RAII guard for acquired resources.
///
/// When dropped, the resource is automatically released.
pub struct ResourceGuard {
    limiter: Arc<LimiterInner>,
    resource: ResourceType,
}

impl ResourceGuard {
    /// Manually release this resource.
    ///
    /// This is called automatically when the guard is dropped.
    pub fn release(self) {
        // Just drop self, which triggers the Drop impl
        drop(self);
    }
}

impl Drop for ResourceGuard {
    fn drop(&mut self) {
        match &self.resource {
            ResourceType::Memory(bytes) => {
                self.limiter.memory_used.fetch_sub(*bytes, Ordering::SeqCst);
            }
            ResourceType::Connection => {
                self.limiter.connections_used.fetch_sub(1, Ordering::SeqCst);
            }
            ResourceType::FileDescriptor => {
                self.limiter.fds_used.fetch_sub(1, Ordering::SeqCst);
            }
        }
    }
}

impl std::fmt::Debug for ResourceGuard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ResourceGuard")
            .field("resource", &self.resource)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unlimited_resources() {
        let limiter = ResourceLimiter::new();

        // Should succeed without limits
        let _mem = limiter.allocate(1000).unwrap();
        let _conn = limiter.acquire_connection().unwrap();
        let _fd = limiter.acquire_fd().unwrap();
    }

    #[test]
    fn test_memory_limit() {
        let limiter = ResourceLimiter::new().with_memory_limit(100);

        // First allocation succeeds
        let _guard = limiter.allocate(60).unwrap();

        // Second allocation within limit succeeds
        let _guard2 = limiter.allocate(30).unwrap();

        // Third allocation exceeds limit
        assert!(limiter.allocate(20).is_err());

        let stats = limiter.stats();
        assert_eq!(stats.memory_exhaustions, 1);
    }

    #[test]
    fn test_memory_release() {
        let limiter = ResourceLimiter::new().with_memory_limit(100);

        {
            let _guard = limiter.allocate(100).unwrap();
            assert!(limiter.allocate(1).is_err()); // At limit
        }
        // Guard dropped, memory released

        // Now we can allocate again
        let _guard = limiter.allocate(100).unwrap();
    }

    #[test]
    fn test_connection_limit() {
        let limiter = ResourceLimiter::new().with_connection_limit(2);

        let conn1 = limiter.acquire_connection().unwrap();
        let conn2 = limiter.acquire_connection().unwrap();

        // Third fails
        assert!(limiter.acquire_connection().is_err());

        // Release one
        drop(conn1);

        // Now we can acquire
        let _conn3 = limiter.acquire_connection().unwrap();

        drop(conn2);

        let stats = limiter.stats();
        assert_eq!(stats.connection_attempts, 4);
        assert_eq!(stats.connection_exhaustions, 1);
    }

    #[test]
    fn test_fd_limit() {
        let limiter = ResourceLimiter::new().with_fd_limit(3);

        let _fd1 = limiter.acquire_fd().unwrap();
        let _fd2 = limiter.acquire_fd().unwrap();
        let _fd3 = limiter.acquire_fd().unwrap();

        // Fourth fails
        assert!(limiter.acquire_fd().is_err());

        let stats = limiter.stats();
        assert_eq!(stats.fd_exhaustions, 1);
    }

    #[test]
    fn test_status() {
        let limiter = ResourceLimiter::new()
            .with_memory_limit(1000)
            .with_connection_limit(10);

        let _mem = limiter.allocate(300).unwrap();
        let _conn = limiter.acquire_connection().unwrap();

        let status = limiter.status();
        assert_eq!(status.memory_limit, 1000);
        assert_eq!(status.memory_used, 300);
        assert_eq!(status.memory_available, 700);
        assert_eq!(status.connection_limit, 10);
        assert_eq!(status.connections_used, 1);
        assert_eq!(status.connections_available, 9);
    }

    #[test]
    fn test_peak_tracking() {
        let limiter = ResourceLimiter::new().with_memory_limit(1000);

        let m1 = limiter.allocate(100).unwrap();
        let m2 = limiter.allocate(200).unwrap();

        drop(m1);
        drop(m2);

        let stats = limiter.stats();
        assert_eq!(stats.peak_memory, 300);
    }

    #[test]
    fn test_reset() {
        let limiter = ResourceLimiter::new().with_memory_limit(1000);

        // Use some resources (don't drop the guard to simulate leak)
        let guard = limiter.allocate(500).unwrap();
        std::mem::forget(guard); // Simulate not releasing

        limiter.reset();

        let status = limiter.status();
        assert_eq!(status.memory_used, 0);

        let stats = limiter.stats();
        assert_eq!(stats.memory_allocations, 0);
    }

    #[test]
    fn test_clone_shares_state() {
        let limiter1 = ResourceLimiter::new().with_connection_limit(2);
        let limiter2 = limiter1.clone();

        let _conn1 = limiter1.acquire_connection().unwrap();
        let _conn2 = limiter2.acquire_connection().unwrap();

        // Both clones share the limit
        assert!(limiter1.acquire_connection().is_err());
        assert!(limiter2.acquire_connection().is_err());
    }

    #[test]
    fn test_resource_guard_debug() {
        let limiter = ResourceLimiter::new();
        let guard = limiter.acquire_connection().unwrap();
        let debug = format!("{:?}", guard);
        assert!(debug.contains("ResourceGuard"));
    }
}
