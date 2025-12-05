//! Stream assertion utilities for testing async streams.
//!
//! This module provides fluent assertions for testing [`Stream`] implementations.
//!
//! # Example
//!
//! ```rust,ignore
//! use testkit_async::assertions::assert_stream;
//! use futures::stream;
//!
//! let s = stream::iter(vec![1, 2, 3]);
//! assert_stream(s)
//!     .next_eq(1).await
//!     .next_eq(2).await
//!     .next_eq(3).await
//!     .ends().await;
//! ```

use std::fmt::Debug;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

use futures_core::Stream;
use pin_project_lite::pin_project;

/// Create a stream assertion builder.
///
/// # Example
///
/// ```rust,ignore
/// use testkit_async::assertions::assert_stream;
/// use futures::stream;
///
/// let s = stream::iter(vec![1, 2, 3]);
/// assert_stream(s)
///     .next_eq(1).await
///     .next_eq(2).await
///     .ends().await;
/// ```
pub fn assert_stream<S>(stream: S) -> StreamAssertion<S>
where
    S: Stream,
{
    StreamAssertion { stream }
}

/// Fluent assertion builder for streams.
///
/// Created by [`assert_stream`]. Provides chainable assertions
/// for testing stream behavior.
pub struct StreamAssertion<S> {
    stream: S,
}

impl<S> StreamAssertion<S>
where
    S: Stream + Unpin,
{
    /// Assert the next element equals the expected value.
    ///
    /// # Panics
    ///
    /// Panics if the next element doesn't equal `expected` or if the stream ends.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// assert_stream(stream::iter(vec![1, 2]))
    ///     .next_eq(1).await
    ///     .next_eq(2).await;
    /// ```
    pub fn next_eq<T>(self, expected: T) -> NextEqFuture<S, T>
    where
        S::Item: PartialEq<T> + Debug,
        T: Debug,
    {
        NextEqFuture {
            stream: Some(self.stream),
            expected: Some(expected),
        }
    }

    /// Assert the next element matches a predicate.
    ///
    /// # Panics
    ///
    /// Panics if the next element doesn't match or if the stream ends.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// assert_stream(stream::iter(vec![1, 2, 3]))
    ///     .next_matches(|x| *x > 0).await
    ///     .next_matches(|x| *x % 2 == 0).await;
    /// ```
    pub fn next_matches<F>(self, predicate: F) -> NextMatchesFuture<S, F>
    where
        F: FnOnce(&S::Item) -> bool,
        S::Item: Debug,
    {
        NextMatchesFuture {
            stream: Some(self.stream),
            predicate: Some(predicate),
        }
    }

    /// Skip the next N elements.
    ///
    /// # Panics
    ///
    /// Panics if the stream ends before skipping N elements.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// assert_stream(stream::iter(vec![1, 2, 3, 4, 5]))
    ///     .skip(3).await
    ///     .next_eq(4).await;
    /// ```
    pub fn skip(self, count: usize) -> SkipFuture<S> {
        SkipFuture {
            stream: Some(self.stream),
            remaining: count,
        }
    }

    /// Assert the stream ends (no more elements).
    ///
    /// # Panics
    ///
    /// Panics if the stream produces another element.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// assert_stream(stream::iter(vec![1]))
    ///     .next_eq(1).await
    ///     .ends().await;
    /// ```
    pub fn ends(self) -> EndsFuture<S>
    where
        S::Item: Debug,
    {
        EndsFuture {
            stream: self.stream,
        }
    }

    /// Collect the stream and assert it equals the expected values.
    ///
    /// # Panics
    ///
    /// Panics if the collected values don't match expected.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// assert_stream(stream::iter(vec![1, 2, 3]))
    ///     .collect_eq(vec![1, 2, 3]).await;
    /// ```
    pub fn collect_eq<C>(self, expected: C) -> CollectEqFuture<S, C>
    where
        S::Item: PartialEq + Debug,
        C: AsRef<[S::Item]> + Debug,
    {
        CollectEqFuture {
            stream: self.stream,
            expected,
            collected: Vec::new(),
        }
    }

    /// Assert the stream has exactly the expected length.
    ///
    /// Consumes the entire stream.
    ///
    /// # Panics
    ///
    /// Panics if the stream length doesn't match.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// assert_stream(stream::iter(vec![1, 2, 3]))
    ///     .has_length(3).await;
    /// ```
    pub fn has_length(self, expected: usize) -> HasLengthFuture<S> {
        HasLengthFuture {
            stream: self.stream,
            expected,
            count: 0,
        }
    }

    /// Assert all elements match the predicate.
    ///
    /// Consumes the entire stream.
    ///
    /// # Panics
    ///
    /// Panics if any element doesn't match.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// assert_stream(stream::iter(vec![2, 4, 6]))
    ///     .all_match(|x| x % 2 == 0).await;
    /// ```
    pub fn all_match<F>(self, predicate: F) -> AllMatchFuture<S, F>
    where
        F: FnMut(&S::Item) -> bool,
        S::Item: Debug,
    {
        AllMatchFuture {
            stream: self.stream,
            predicate,
            index: 0,
        }
    }

    /// Assert any element matches the predicate.
    ///
    /// Consumes elements until a match is found or the stream ends.
    ///
    /// # Panics
    ///
    /// Panics if no element matches.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// assert_stream(stream::iter(vec![1, 2, 3, 4, 5]))
    ///     .any_match(|x| *x == 3).await;
    /// ```
    pub fn any_match<F>(self, predicate: F) -> AnyMatchFuture<S, F>
    where
        F: FnMut(&S::Item) -> bool,
        S::Item: Debug,
    {
        AnyMatchFuture {
            stream: self.stream,
            predicate,
        }
    }

    /// Get the inner stream.
    ///
    /// Use this to access the stream after assertions.
    #[must_use]
    pub fn into_inner(self) -> S {
        self.stream
    }
}

// Future implementations for each assertion

pin_project! {
    /// Future for `next_eq` assertion.
    pub struct NextEqFuture<S, T> {
        stream: Option<S>,
        expected: Option<T>,
    }
}

impl<S, T> Future for NextEqFuture<S, T>
where
    S: Stream + Unpin,
    S::Item: PartialEq<T> + Debug,
    T: Debug,
{
    type Output = StreamAssertion<S>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();
        let stream = this.stream.as_mut().expect("polled after completion");

        match Pin::new(stream).poll_next(cx) {
            Poll::Ready(Some(item)) => {
                let expected = this.expected.take().expect("polled after completion");
                assert!(
                    item == expected,
                    "stream assertion failed: expected {:?}, got {:?}",
                    expected,
                    item
                );
                Poll::Ready(StreamAssertion {
                    stream: this.stream.take().unwrap(),
                })
            }
            Poll::Ready(None) => {
                let expected = this.expected.take().expect("polled after completion");
                panic!(
                    "stream assertion failed: expected {:?}, but stream ended",
                    expected
                );
            }
            Poll::Pending => Poll::Pending,
        }
    }
}

pin_project! {
    /// Future for `next_matches` assertion.
    pub struct NextMatchesFuture<S, F> {
        stream: Option<S>,
        predicate: Option<F>,
    }
}

impl<S, F> Future for NextMatchesFuture<S, F>
where
    S: Stream + Unpin,
    F: FnOnce(&S::Item) -> bool,
    S::Item: Debug,
{
    type Output = StreamAssertion<S>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();
        let stream = this.stream.as_mut().expect("polled after completion");

        match Pin::new(stream).poll_next(cx) {
            Poll::Ready(Some(item)) => {
                let predicate = this.predicate.take().expect("polled after completion");
                assert!(
                    predicate(&item),
                    "stream assertion failed: item {:?} did not match predicate",
                    item
                );
                Poll::Ready(StreamAssertion {
                    stream: this.stream.take().unwrap(),
                })
            }
            Poll::Ready(None) => {
                panic!("stream assertion failed: expected item matching predicate, but stream ended");
            }
            Poll::Pending => Poll::Pending,
        }
    }
}

pin_project! {
    /// Future for `skip` operation.
    pub struct SkipFuture<S> {
        stream: Option<S>,
        remaining: usize,
    }
}

impl<S> Future for SkipFuture<S>
where
    S: Stream + Unpin,
{
    type Output = StreamAssertion<S>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();
        let stream = this.stream.as_mut().expect("polled after completion");

        while *this.remaining > 0 {
            match Pin::new(&mut *stream).poll_next(cx) {
                Poll::Ready(Some(_)) => {
                    *this.remaining -= 1;
                }
                Poll::Ready(None) => {
                    panic!(
                        "stream assertion failed: expected to skip {} more elements, but stream ended",
                        this.remaining
                    );
                }
                Poll::Pending => return Poll::Pending,
            }
        }

        Poll::Ready(StreamAssertion {
            stream: this.stream.take().unwrap(),
        })
    }
}

pin_project! {
    /// Future for `ends` assertion.
    pub struct EndsFuture<S> {
        #[pin]
        stream: S,
    }
}

impl<S> Future for EndsFuture<S>
where
    S: Stream + Unpin,
    S::Item: Debug,
{
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();
        let stream = this.stream.get_mut();

        match Pin::new(stream).poll_next(cx) {
            Poll::Ready(Some(item)) => {
                panic!(
                    "stream assertion failed: expected stream to end, got {:?}",
                    item
                );
            }
            Poll::Ready(None) => Poll::Ready(()),
            Poll::Pending => Poll::Pending,
        }
    }
}

pin_project! {
    /// Future for `collect_eq` assertion.
    pub struct CollectEqFuture<S: Stream, C> {
        #[pin]
        stream: S,
        expected: C,
        collected: Vec<S::Item>,
    }
}

impl<S, C> Future for CollectEqFuture<S, C>
where
    S: Stream + Unpin,
    S::Item: PartialEq + Debug,
    C: AsRef<[S::Item]> + Debug,
{
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();
        let stream = this.stream.get_mut();

        loop {
            match Pin::new(&mut *stream).poll_next(cx) {
                Poll::Ready(Some(item)) => {
                    this.collected.push(item);
                }
                Poll::Ready(None) => {
                    let expected = this.expected.as_ref();
                    assert!(
                        this.collected.as_slice() == expected,
                        "stream assertion failed: expected {:?}, got {:?}",
                        expected,
                        this.collected
                    );
                    return Poll::Ready(());
                }
                Poll::Pending => return Poll::Pending,
            }
        }
    }
}

pin_project! {
    /// Future for `has_length` assertion.
    pub struct HasLengthFuture<S> {
        #[pin]
        stream: S,
        expected: usize,
        count: usize,
    }
}

impl<S> Future for HasLengthFuture<S>
where
    S: Stream + Unpin,
{
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();
        let stream = this.stream.get_mut();

        loop {
            match Pin::new(&mut *stream).poll_next(cx) {
                Poll::Ready(Some(_)) => {
                    *this.count += 1;
                }
                Poll::Ready(None) => {
                    assert!(
                        *this.count == *this.expected,
                        "stream assertion failed: expected length {}, got {}",
                        this.expected,
                        this.count
                    );
                    return Poll::Ready(());
                }
                Poll::Pending => return Poll::Pending,
            }
        }
    }
}

pin_project! {
    /// Future for `all_match` assertion.
    pub struct AllMatchFuture<S, F> {
        #[pin]
        stream: S,
        predicate: F,
        index: usize,
    }
}

impl<S, F> Future for AllMatchFuture<S, F>
where
    S: Stream + Unpin,
    F: FnMut(&S::Item) -> bool,
    S::Item: Debug,
{
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();
        let stream = this.stream.get_mut();

        loop {
            match Pin::new(&mut *stream).poll_next(cx) {
                Poll::Ready(Some(item)) => {
                    assert!(
                        (this.predicate)(&item),
                        "stream assertion failed: item at index {} ({:?}) did not match predicate",
                        this.index,
                        item
                    );
                    *this.index += 1;
                }
                Poll::Ready(None) => {
                    return Poll::Ready(());
                }
                Poll::Pending => return Poll::Pending,
            }
        }
    }
}

pin_project! {
    /// Future for `any_match` assertion.
    pub struct AnyMatchFuture<S, F> {
        #[pin]
        stream: S,
        predicate: F,
    }
}

impl<S, F> Future for AnyMatchFuture<S, F>
where
    S: Stream + Unpin,
    F: FnMut(&S::Item) -> bool,
    S::Item: Debug,
{
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();
        let stream = this.stream.get_mut();

        loop {
            match Pin::new(&mut *stream).poll_next(cx) {
                Poll::Ready(Some(item)) => {
                    if (this.predicate)(&item) {
                        return Poll::Ready(());
                    }
                }
                Poll::Ready(None) => {
                    panic!("stream assertion failed: no element matched the predicate");
                }
                Poll::Pending => return Poll::Pending,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::stream;

    #[tokio::test]
    async fn test_next_eq() {
        let s = stream::iter(vec![1, 2, 3]);
        assert_stream(s).next_eq(1).await.next_eq(2).await.next_eq(3).await;
    }

    #[tokio::test]
    async fn test_next_matches() {
        let s = stream::iter(vec![1, 2, 3]);
        assert_stream(s)
            .next_matches(|x| *x == 1)
            .await
            .next_matches(|x| *x % 2 == 0)
            .await
            .next_matches(|x| *x > 2)
            .await;
    }

    #[tokio::test]
    async fn test_skip() {
        let s = stream::iter(vec![1, 2, 3, 4, 5]);
        assert_stream(s).skip(3).await.next_eq(4).await.next_eq(5).await;
    }

    #[tokio::test]
    async fn test_ends() {
        let s = stream::iter(vec![1]);
        assert_stream(s).next_eq(1).await.ends().await;
    }

    #[tokio::test]
    async fn test_collect_eq() {
        let s = stream::iter(vec![1, 2, 3]);
        assert_stream(s).collect_eq(vec![1, 2, 3]).await;
    }

    #[tokio::test]
    async fn test_has_length() {
        let s = stream::iter(vec![1, 2, 3, 4, 5]);
        assert_stream(s).has_length(5).await;
    }

    #[tokio::test]
    async fn test_all_match() {
        let s = stream::iter(vec![2, 4, 6, 8]);
        assert_stream(s).all_match(|x| x % 2 == 0).await;
    }

    #[tokio::test]
    async fn test_any_match() {
        let s = stream::iter(vec![1, 2, 3, 4, 5]);
        assert_stream(s).any_match(|x| *x == 3).await;
    }

    #[tokio::test]
    async fn test_empty_stream_ends() {
        let s = stream::iter(Vec::<i32>::new());
        assert_stream(s).ends().await;
    }

    #[tokio::test]
    async fn test_empty_stream_has_length_zero() {
        let s = stream::iter(Vec::<i32>::new());
        assert_stream(s).has_length(0).await;
    }

    #[tokio::test]
    async fn test_all_match_empty_stream() {
        let s = stream::iter(Vec::<i32>::new());
        // Empty stream trivially matches all
        assert_stream(s).all_match(|_| false).await;
    }

    #[tokio::test]
    #[should_panic(expected = "expected 99")]
    async fn test_next_eq_fails() {
        let s = stream::iter(vec![1, 2, 3]);
        assert_stream(s).next_eq(99).await;
    }

    #[tokio::test]
    #[should_panic(expected = "stream ended")]
    async fn test_next_eq_on_empty_fails() {
        let s = stream::iter(Vec::<i32>::new());
        assert_stream(s).next_eq(1).await;
    }

    #[tokio::test]
    #[should_panic(expected = "did not match predicate")]
    async fn test_next_matches_fails() {
        let s = stream::iter(vec![1, 2, 3]);
        assert_stream(s).next_matches(|x| *x > 100).await;
    }

    #[tokio::test]
    #[should_panic(expected = "expected to skip")]
    async fn test_skip_fails_on_short_stream() {
        let s = stream::iter(vec![1, 2]);
        assert_stream(s).skip(5).await;
    }

    #[tokio::test]
    #[should_panic(expected = "expected stream to end")]
    async fn test_ends_fails() {
        let s = stream::iter(vec![1, 2, 3]);
        assert_stream(s).ends().await;
    }

    #[tokio::test]
    #[should_panic(expected = "expected length 10")]
    async fn test_has_length_fails() {
        let s = stream::iter(vec![1, 2, 3]);
        assert_stream(s).has_length(10).await;
    }

    #[tokio::test]
    #[should_panic(expected = "did not match predicate")]
    async fn test_all_match_fails() {
        let s = stream::iter(vec![2, 4, 5, 8]);
        assert_stream(s).all_match(|x| x % 2 == 0).await;
    }

    #[tokio::test]
    #[should_panic(expected = "no element matched")]
    async fn test_any_match_fails() {
        let s = stream::iter(vec![1, 2, 3]);
        assert_stream(s).any_match(|x| *x > 100).await;
    }
}
