//! Mock channel implementation for testing message passing.
//!
//! This module provides [`MockChannel`] for testing async code that uses channels.
//!
//! # Example
//!
//! ```rust
//! use testkit_async::mock::MockChannel;
//!
//! let (tx, rx) = MockChannel::<i32>::unbounded();
//!
//! // Send messages
//! tx.send(1).unwrap();
//! tx.send(2).unwrap();
//!
//! // Check sent messages
//! assert_eq!(tx.sent_messages(), vec![1, 2]);
//!
//! // Receive messages
//! assert_eq!(rx.try_recv().unwrap(), 1);
//! assert_eq!(rx.try_recv().unwrap(), 2);
//! ```

use std::collections::VecDeque;
use std::fmt::Debug;
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use std::task::{Context, Poll, Waker};

use parking_lot::Mutex;

/// A mock channel for testing.
///
/// Provides inspection capabilities and controllable behavior.
/// This struct is just a namespace for the channel constructors.
pub struct MockChannel<T> {
    _phantom: std::marker::PhantomData<T>,
}

struct ChannelInner<T> {
    /// Messages waiting to be received.
    queue: Mutex<VecDeque<T>>,
    /// History of all sent messages.
    sent_history: Mutex<Vec<T>>,
    /// Channel capacity (0 = unbounded).
    capacity: usize,
    /// Whether the sender is closed.
    sender_closed: AtomicBool,
    /// Whether backpressure is applied.
    backpressure: AtomicBool,
    /// Waker for receivers waiting for messages.
    receiver_waker: Mutex<Option<Waker>>,
    /// Waker for senders waiting for capacity.
    sender_waker: Mutex<Option<Waker>>,
    /// Number of messages dropped.
    dropped_count: AtomicUsize,
}

impl<T: Clone> MockChannel<T> {
    /// Create an unbounded mock channel.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::mock::MockChannel;
    ///
    /// let (tx, rx) = MockChannel::<i32>::unbounded();
    /// ```
    pub fn unbounded() -> (MockSender<T>, MockReceiver<T>) {
        Self::with_capacity(0)
    }

    /// Create a bounded mock channel with the given capacity.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::mock::MockChannel;
    ///
    /// let (tx, rx) = MockChannel::<i32>::bounded(10);
    /// ```
    pub fn bounded(capacity: usize) -> (MockSender<T>, MockReceiver<T>) {
        Self::with_capacity(capacity)
    }

    fn with_capacity(capacity: usize) -> (MockSender<T>, MockReceiver<T>) {
        let inner = Arc::new(ChannelInner {
            queue: Mutex::new(VecDeque::new()),
            sent_history: Mutex::new(Vec::new()),
            capacity,
            sender_closed: AtomicBool::new(false),
            backpressure: AtomicBool::new(false),
            receiver_waker: Mutex::new(None),
            sender_waker: Mutex::new(None),
            dropped_count: AtomicUsize::new(0),
        });

        (
            MockSender {
                inner: Arc::clone(&inner),
            },
            MockReceiver { inner },
        )
    }
}

/// Error returned when sending to a closed channel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SendError<T>(pub T);

impl<T> std::fmt::Display for SendError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "sending on a closed channel")
    }
}

impl<T: Debug> std::error::Error for SendError<T> {}

/// Error returned when receiving from a closed empty channel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecvError;

impl std::fmt::Display for RecvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "receiving on a closed channel")
    }
}

impl std::error::Error for RecvError {}

/// Error returned when trying to receive without blocking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TryRecvError {
    /// Channel is empty but not closed.
    Empty,
    /// Channel is closed and empty.
    Disconnected,
}

impl std::fmt::Display for TryRecvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "channel is empty"),
            Self::Disconnected => write!(f, "channel is disconnected"),
        }
    }
}

impl std::error::Error for TryRecvError {}

/// Sending half of a mock channel.
pub struct MockSender<T> {
    inner: Arc<ChannelInner<T>>,
}

impl<T: Clone> MockSender<T> {
    /// Send a value on the channel.
    ///
    /// Returns an error if the channel is closed.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::mock::MockChannel;
    ///
    /// let (tx, _rx) = MockChannel::unbounded();
    /// tx.send(42).unwrap();
    /// ```
    pub fn send(&self, value: T) -> Result<(), SendError<T>> {
        if self.inner.sender_closed.load(Ordering::SeqCst) {
            return Err(SendError(value));
        }

        // Check backpressure
        if self.inner.backpressure.load(Ordering::SeqCst) {
            return Err(SendError(value));
        }

        // Check capacity
        let mut queue = self.inner.queue.lock();
        if self.inner.capacity > 0 && queue.len() >= self.inner.capacity {
            self.inner.dropped_count.fetch_add(1, Ordering::SeqCst);
            return Err(SendError(value));
        }

        // Record in history
        self.inner.sent_history.lock().push(value.clone());

        // Add to queue
        queue.push_back(value);

        // Wake receiver
        if let Some(waker) = self.inner.receiver_waker.lock().take() {
            waker.wake();
        }

        Ok(())
    }

    /// Send a value asynchronously.
    ///
    /// Waits if the channel is at capacity or under backpressure.
    pub fn send_async(&self, value: T) -> SendFuture<'_, T> {
        SendFuture {
            sender: self,
            value: Some(value),
        }
    }

    /// Close the sender.
    ///
    /// After closing, all subsequent sends will fail.
    pub fn close(&self) {
        self.inner.sender_closed.store(true, Ordering::SeqCst);
        // Wake receiver to notify of close
        if let Some(waker) = self.inner.receiver_waker.lock().take() {
            waker.wake();
        }
    }

    /// Check if the sender is closed.
    #[must_use]
    pub fn is_closed(&self) -> bool {
        self.inner.sender_closed.load(Ordering::SeqCst)
    }

    /// Apply backpressure (block sends).
    pub fn apply_backpressure(&self) {
        self.inner.backpressure.store(true, Ordering::SeqCst);
    }

    /// Release backpressure (allow sends).
    pub fn release_backpressure(&self) {
        self.inner.backpressure.store(false, Ordering::SeqCst);
        // Wake any waiting senders
        if let Some(waker) = self.inner.sender_waker.lock().take() {
            waker.wake();
        }
    }

    /// Check if backpressure is applied.
    #[must_use]
    pub fn has_backpressure(&self) -> bool {
        self.inner.backpressure.load(Ordering::SeqCst)
    }

    /// Get all sent messages (history).
    #[must_use]
    pub fn sent_messages(&self) -> Vec<T> {
        self.inner.sent_history.lock().clone()
    }

    /// Get the count of sent messages.
    #[must_use]
    pub fn message_count(&self) -> usize {
        self.inner.sent_history.lock().len()
    }

    /// Clear the message history.
    pub fn clear_history(&self) {
        self.inner.sent_history.lock().clear();
    }

    /// Get the count of dropped messages.
    #[must_use]
    pub fn dropped_count(&self) -> usize {
        self.inner.dropped_count.load(Ordering::SeqCst)
    }

    /// Get the current queue length.
    #[must_use]
    pub fn queue_len(&self) -> usize {
        self.inner.queue.lock().len()
    }
}

impl<T> Clone for MockSender<T> {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl<T: Debug + Clone> Debug for MockSender<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MockSender")
            .field("closed", &self.is_closed())
            .field("backpressure", &self.has_backpressure())
            .field("queue_len", &self.queue_len())
            .field("message_count", &self.message_count())
            .finish()
    }
}

/// Future for async send.
pub struct SendFuture<'a, T> {
    sender: &'a MockSender<T>,
    value: Option<T>,
}

impl<T> Unpin for SendFuture<'_, T> {}

impl<T: Clone> Future for SendFuture<'_, T> {
    type Output = Result<(), SendError<T>>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let value = match self.value.take() {
            Some(v) => v,
            None => panic!("polled after completion"),
        };

        // Check if closed
        if self.sender.inner.sender_closed.load(Ordering::SeqCst) {
            return Poll::Ready(Err(SendError(value)));
        }

        // Check backpressure
        if self.sender.inner.backpressure.load(Ordering::SeqCst) {
            self.value = Some(value);
            *self.sender.inner.sender_waker.lock() = Some(cx.waker().clone());
            return Poll::Pending;
        }

        // Check capacity
        let mut queue = self.sender.inner.queue.lock();
        if self.sender.inner.capacity > 0 && queue.len() >= self.sender.inner.capacity {
            drop(queue);
            self.value = Some(value);
            *self.sender.inner.sender_waker.lock() = Some(cx.waker().clone());
            return Poll::Pending;
        }

        // Record in history
        self.sender.inner.sent_history.lock().push(value.clone());

        // Add to queue
        queue.push_back(value);

        // Wake receiver
        if let Some(waker) = self.sender.inner.receiver_waker.lock().take() {
            waker.wake();
        }

        Poll::Ready(Ok(()))
    }
}

/// Receiving half of a mock channel.
pub struct MockReceiver<T> {
    inner: Arc<ChannelInner<T>>,
}

impl<T> MockReceiver<T> {
    /// Try to receive a value without blocking.
    ///
    /// Returns `Err(TryRecvError::Empty)` if no messages are available,
    /// or `Err(TryRecvError::Disconnected)` if the sender is closed.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::mock::MockChannel;
    ///
    /// let (tx, rx) = MockChannel::unbounded();
    /// tx.send(42).unwrap();
    /// assert_eq!(rx.try_recv().unwrap(), 42);
    /// ```
    pub fn try_recv(&self) -> Result<T, TryRecvError> {
        let mut queue = self.inner.queue.lock();
        if let Some(value) = queue.pop_front() {
            // Wake sender if waiting
            if let Some(waker) = self.inner.sender_waker.lock().take() {
                waker.wake();
            }
            Ok(value)
        } else if self.inner.sender_closed.load(Ordering::SeqCst) {
            Err(TryRecvError::Disconnected)
        } else {
            Err(TryRecvError::Empty)
        }
    }

    /// Receive a value asynchronously.
    ///
    /// Returns `Err(RecvError)` if the sender is closed and no messages remain.
    pub fn recv(&self) -> RecvFuture<'_, T> {
        RecvFuture { receiver: self }
    }

    /// Check if the channel is closed.
    #[must_use]
    pub fn is_closed(&self) -> bool {
        self.inner.sender_closed.load(Ordering::SeqCst)
    }

    /// Check if there are messages available.
    #[must_use]
    pub fn has_messages(&self) -> bool {
        !self.inner.queue.lock().is_empty()
    }

    /// Get the number of messages in the queue.
    #[must_use]
    pub fn len(&self) -> usize {
        self.inner.queue.lock().len()
    }

    /// Check if the queue is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.inner.queue.lock().is_empty()
    }
}

impl<T: Debug> Debug for MockReceiver<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MockReceiver")
            .field("closed", &self.is_closed())
            .field("queue_len", &self.len())
            .finish()
    }
}

/// Future for async receive.
pub struct RecvFuture<'a, T> {
    receiver: &'a MockReceiver<T>,
}

impl<T> Future for RecvFuture<'_, T> {
    type Output = Result<T, RecvError>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut queue = self.receiver.inner.queue.lock();
        if let Some(value) = queue.pop_front() {
            // Wake sender if waiting
            if let Some(waker) = self.receiver.inner.sender_waker.lock().take() {
                waker.wake();
            }
            Poll::Ready(Ok(value))
        } else if self.receiver.inner.sender_closed.load(Ordering::SeqCst) {
            Poll::Ready(Err(RecvError))
        } else {
            *self.receiver.inner.receiver_waker.lock() = Some(cx.waker().clone());
            Poll::Pending
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unbounded_channel() {
        let (tx, rx) = MockChannel::<i32>::unbounded();
        tx.send(1).unwrap();
        tx.send(2).unwrap();
        tx.send(3).unwrap();

        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv().unwrap(), 2);
        assert_eq!(rx.try_recv().unwrap(), 3);
    }

    #[test]
    fn test_bounded_channel() {
        let (tx, rx) = MockChannel::<i32>::bounded(2);
        tx.send(1).unwrap();
        tx.send(2).unwrap();

        // Third send should fail (at capacity)
        assert!(tx.send(3).is_err());
        assert_eq!(tx.dropped_count(), 1);

        // After receiving, can send again
        assert_eq!(rx.try_recv().unwrap(), 1);
        // Note: sync send doesn't retry, need to send again
    }

    #[test]
    fn test_sent_messages_history() {
        let (tx, _rx) = MockChannel::<i32>::unbounded();
        tx.send(1).unwrap();
        tx.send(2).unwrap();
        tx.send(3).unwrap();

        assert_eq!(tx.sent_messages(), vec![1, 2, 3]);
        assert_eq!(tx.message_count(), 3);
    }

    #[test]
    fn test_clear_history() {
        let (tx, _rx) = MockChannel::<i32>::unbounded();
        tx.send(1).unwrap();
        tx.send(2).unwrap();

        tx.clear_history();

        assert_eq!(tx.sent_messages(), Vec::<i32>::new());
        assert_eq!(tx.message_count(), 0);
    }

    #[test]
    fn test_close_sender() {
        let (tx, rx) = MockChannel::<i32>::unbounded();
        tx.send(1).unwrap();
        tx.close();

        // Can't send after close
        assert!(tx.send(2).is_err());
        assert!(tx.is_closed());

        // Can still receive buffered messages
        assert_eq!(rx.try_recv().unwrap(), 1);

        // Then get disconnected
        assert_eq!(rx.try_recv(), Err(TryRecvError::Disconnected));
    }

    #[test]
    fn test_backpressure() {
        let (tx, _rx) = MockChannel::<i32>::unbounded();

        tx.send(1).unwrap();

        tx.apply_backpressure();
        assert!(tx.has_backpressure());
        assert!(tx.send(2).is_err());

        tx.release_backpressure();
        assert!(!tx.has_backpressure());
        tx.send(3).unwrap();

        assert_eq!(tx.sent_messages(), vec![1, 3]);
    }

    #[test]
    fn test_try_recv_empty() {
        let (_tx, rx) = MockChannel::<i32>::unbounded();
        assert_eq!(rx.try_recv(), Err(TryRecvError::Empty));
    }

    #[test]
    fn test_receiver_properties() {
        let (tx, rx) = MockChannel::<i32>::unbounded();

        assert!(rx.is_empty());
        assert!(!rx.has_messages());
        assert_eq!(rx.len(), 0);

        tx.send(1).unwrap();
        tx.send(2).unwrap();

        assert!(!rx.is_empty());
        assert!(rx.has_messages());
        assert_eq!(rx.len(), 2);
    }

    #[test]
    fn test_sender_clone() {
        let (tx1, rx) = MockChannel::<i32>::unbounded();
        let tx2 = tx1.clone();

        tx1.send(1).unwrap();
        tx2.send(2).unwrap();

        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv().unwrap(), 2);
    }

    #[test]
    fn test_queue_len() {
        let (tx, rx) = MockChannel::<i32>::unbounded();

        assert_eq!(tx.queue_len(), 0);

        tx.send(1).unwrap();
        tx.send(2).unwrap();
        assert_eq!(tx.queue_len(), 2);

        rx.try_recv().unwrap();
        assert_eq!(tx.queue_len(), 1);
    }

    #[tokio::test]
    async fn test_async_send_recv() {
        let (tx, rx) = MockChannel::<i32>::unbounded();

        tx.send_async(1).await.unwrap();
        tx.send_async(2).await.unwrap();

        assert_eq!(rx.recv().await.unwrap(), 1);
        assert_eq!(rx.recv().await.unwrap(), 2);
    }

    #[tokio::test]
    async fn test_async_recv_after_close() {
        let (tx, rx) = MockChannel::<i32>::unbounded();

        tx.send(1).unwrap();
        tx.close();

        // Can receive buffered message
        assert_eq!(rx.recv().await.unwrap(), 1);

        // Then error
        assert!(rx.recv().await.is_err());
    }

    #[test]
    fn test_debug_impls() {
        let (tx, rx) = MockChannel::<i32>::unbounded();
        tx.send(1).unwrap();

        let tx_debug = format!("{:?}", tx);
        assert!(tx_debug.contains("MockSender"));

        let rx_debug = format!("{:?}", rx);
        assert!(rx_debug.contains("MockReceiver"));
    }

    #[test]
    fn test_error_display() {
        let send_err = SendError(42);
        assert!(send_err.to_string().contains("closed channel"));

        let recv_err = RecvError;
        assert!(recv_err.to_string().contains("closed channel"));

        let try_empty = TryRecvError::Empty;
        assert!(try_empty.to_string().contains("empty"));

        let try_disc = TryRecvError::Disconnected;
        assert!(try_disc.to_string().contains("disconnected"));
    }
}
