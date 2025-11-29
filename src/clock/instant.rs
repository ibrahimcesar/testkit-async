//! Mock instant type for virtual time.

use std::ops::{Add, AddAssign, Sub, SubAssign};
use std::time::Duration;

use super::MockClock;

/// A mock instant that represents a point in virtual time.
///
/// `MockInstant` mirrors the API of [`std::time::Instant`] but uses virtual time
/// from a [`MockClock`] instead of real system time.
///
/// # Example
///
/// ```rust
/// use testkit_async::clock::{MockClock, MockInstant};
/// use std::time::Duration;
///
/// let clock = MockClock::new();
/// let start = MockInstant::now(&clock);
///
/// clock.advance(Duration::from_secs(10));
/// let end = MockInstant::now(&clock);
///
/// assert_eq!(end.duration_since(start), Duration::from_secs(10));
/// assert_eq!(start.elapsed(&clock), Duration::from_secs(10));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MockInstant {
    inner: Duration,
}

impl MockInstant {
    /// Returns the current virtual time as a `MockInstant`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::{MockClock, MockInstant};
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::new();
    /// let instant = MockInstant::now(&clock);
    ///
    /// clock.advance(Duration::from_secs(5));
    /// let later = MockInstant::now(&clock);
    ///
    /// assert!(later > instant);
    /// ```
    #[must_use]
    pub fn now(clock: &MockClock) -> Self {
        Self { inner: clock.now() }
    }

    /// Returns the amount of time elapsed from another instant to this one.
    ///
    /// # Panics
    ///
    /// Panics if `earlier` is later than `self`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::{MockClock, MockInstant};
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::new();
    /// let earlier = MockInstant::now(&clock);
    ///
    /// clock.advance(Duration::from_secs(5));
    /// let later = MockInstant::now(&clock);
    ///
    /// assert_eq!(later.duration_since(earlier), Duration::from_secs(5));
    /// ```
    #[must_use]
    pub fn duration_since(&self, earlier: MockInstant) -> Duration {
        self.checked_duration_since(earlier)
            .expect("earlier instant is later than self")
    }

    /// Returns the amount of time elapsed from another instant to this one,
    /// or `None` if that instant is later than this one.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::{MockClock, MockInstant};
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::new();
    /// let earlier = MockInstant::now(&clock);
    ///
    /// clock.advance(Duration::from_secs(5));
    /// let later = MockInstant::now(&clock);
    ///
    /// assert_eq!(later.checked_duration_since(earlier), Some(Duration::from_secs(5)));
    /// assert_eq!(earlier.checked_duration_since(later), None);
    /// ```
    #[must_use]
    pub fn checked_duration_since(&self, earlier: MockInstant) -> Option<Duration> {
        self.inner.checked_sub(earlier.inner)
    }

    /// Returns the amount of time elapsed from another instant to this one,
    /// or zero if that instant is later than this one.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::{MockClock, MockInstant};
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::new();
    /// let earlier = MockInstant::now(&clock);
    ///
    /// clock.advance(Duration::from_secs(5));
    /// let later = MockInstant::now(&clock);
    ///
    /// assert_eq!(later.saturating_duration_since(earlier), Duration::from_secs(5));
    /// assert_eq!(earlier.saturating_duration_since(later), Duration::ZERO);
    /// ```
    #[must_use]
    pub fn saturating_duration_since(&self, earlier: MockInstant) -> Duration {
        self.checked_duration_since(earlier)
            .unwrap_or(Duration::ZERO)
    }

    /// Returns the amount of time elapsed since this instant was created.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::{MockClock, MockInstant};
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::new();
    /// let instant = MockInstant::now(&clock);
    ///
    /// clock.advance(Duration::from_secs(5));
    /// assert_eq!(instant.elapsed(&clock), Duration::from_secs(5));
    ///
    /// clock.advance(Duration::from_secs(3));
    /// assert_eq!(instant.elapsed(&clock), Duration::from_secs(8));
    /// ```
    #[must_use]
    pub fn elapsed(&self, clock: &MockClock) -> Duration {
        MockInstant::now(clock).duration_since(*self)
    }

    /// Returns `Some(t)` where `t` is the time `self + duration` if `t` can be
    /// represented as `MockInstant`, or `None` otherwise.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::{MockClock, MockInstant};
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::new();
    /// let instant = MockInstant::now(&clock);
    ///
    /// let later = instant.checked_add(Duration::from_secs(5));
    /// assert!(later.is_some());
    /// ```
    #[must_use]
    pub fn checked_add(&self, duration: Duration) -> Option<MockInstant> {
        self.inner
            .checked_add(duration)
            .map(|d| MockInstant { inner: d })
    }

    /// Returns `Some(t)` where `t` is the time `self - duration` if `t` can be
    /// represented as `MockInstant`, or `None` otherwise.
    ///
    /// # Example
    ///
    /// ```rust
    /// use testkit_async::clock::{MockClock, MockInstant};
    /// use std::time::Duration;
    ///
    /// let clock = MockClock::with_start_time(Duration::from_secs(10));
    /// let instant = MockInstant::now(&clock);
    ///
    /// let earlier = instant.checked_sub(Duration::from_secs(5));
    /// assert!(earlier.is_some());
    ///
    /// // Cannot go before time zero
    /// let too_early = instant.checked_sub(Duration::from_secs(20));
    /// assert!(too_early.is_none());
    /// ```
    #[must_use]
    pub fn checked_sub(&self, duration: Duration) -> Option<MockInstant> {
        self.inner
            .checked_sub(duration)
            .map(|d| MockInstant { inner: d })
    }

    /// Returns the inner duration (time since epoch).
    ///
    /// This is useful for serialization or debugging.
    #[must_use]
    pub fn as_duration(&self) -> Duration {
        self.inner
    }

    /// Creates a `MockInstant` from a raw duration.
    ///
    /// This is the inverse of [`as_duration`](Self::as_duration).
    #[must_use]
    pub fn from_duration(duration: Duration) -> Self {
        Self { inner: duration }
    }
}

impl Add<Duration> for MockInstant {
    type Output = MockInstant;

    fn add(self, other: Duration) -> MockInstant {
        self.checked_add(other)
            .expect("overflow when adding duration to instant")
    }
}

impl AddAssign<Duration> for MockInstant {
    fn add_assign(&mut self, other: Duration) {
        *self = *self + other;
    }
}

impl Sub<Duration> for MockInstant {
    type Output = MockInstant;

    fn sub(self, other: Duration) -> MockInstant {
        self.checked_sub(other)
            .expect("overflow when subtracting duration from instant")
    }
}

impl SubAssign<Duration> for MockInstant {
    fn sub_assign(&mut self, other: Duration) {
        *self = *self - other;
    }
}

impl Sub<MockInstant> for MockInstant {
    type Output = Duration;

    fn sub(self, other: MockInstant) -> Duration {
        self.duration_since(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_now() {
        let clock = MockClock::new();
        let instant = MockInstant::now(&clock);
        assert_eq!(instant.as_duration(), Duration::ZERO);

        clock.advance(Duration::from_secs(10));
        let instant2 = MockInstant::now(&clock);
        assert_eq!(instant2.as_duration(), Duration::from_secs(10));
    }

    #[test]
    fn test_duration_since() {
        let clock = MockClock::new();
        let earlier = MockInstant::now(&clock);

        clock.advance(Duration::from_secs(5));
        let later = MockInstant::now(&clock);

        assert_eq!(later.duration_since(earlier), Duration::from_secs(5));
    }

    #[test]
    #[should_panic(expected = "earlier instant is later than self")]
    fn test_duration_since_panics_if_earlier_is_later() {
        let clock = MockClock::new();
        let earlier = MockInstant::now(&clock);

        clock.advance(Duration::from_secs(5));
        let later = MockInstant::now(&clock);

        let _ = earlier.duration_since(later);
    }

    #[test]
    fn test_checked_duration_since() {
        let clock = MockClock::new();
        let earlier = MockInstant::now(&clock);

        clock.advance(Duration::from_secs(5));
        let later = MockInstant::now(&clock);

        assert_eq!(
            later.checked_duration_since(earlier),
            Some(Duration::from_secs(5))
        );
        assert_eq!(earlier.checked_duration_since(later), None);
    }

    #[test]
    fn test_saturating_duration_since() {
        let clock = MockClock::new();
        let earlier = MockInstant::now(&clock);

        clock.advance(Duration::from_secs(5));
        let later = MockInstant::now(&clock);

        assert_eq!(
            later.saturating_duration_since(earlier),
            Duration::from_secs(5)
        );
        assert_eq!(earlier.saturating_duration_since(later), Duration::ZERO);
    }

    #[test]
    fn test_elapsed() {
        let clock = MockClock::new();
        let instant = MockInstant::now(&clock);

        clock.advance(Duration::from_secs(5));
        assert_eq!(instant.elapsed(&clock), Duration::from_secs(5));

        clock.advance(Duration::from_secs(3));
        assert_eq!(instant.elapsed(&clock), Duration::from_secs(8));
    }

    #[test]
    fn test_checked_add() {
        let clock = MockClock::new();
        let instant = MockInstant::now(&clock);

        let later = instant.checked_add(Duration::from_secs(5));
        assert_eq!(
            later,
            Some(MockInstant::from_duration(Duration::from_secs(5)))
        );
    }

    #[test]
    fn test_checked_sub() {
        let clock = MockClock::with_start_time(Duration::from_secs(10));
        let instant = MockInstant::now(&clock);

        let earlier = instant.checked_sub(Duration::from_secs(5));
        assert_eq!(
            earlier,
            Some(MockInstant::from_duration(Duration::from_secs(5)))
        );

        let too_early = instant.checked_sub(Duration::from_secs(20));
        assert_eq!(too_early, None);
    }

    #[test]
    fn test_add_duration() {
        let instant = MockInstant::from_duration(Duration::from_secs(5));
        let later = instant + Duration::from_secs(3);
        assert_eq!(later.as_duration(), Duration::from_secs(8));
    }

    #[test]
    fn test_add_assign() {
        let mut instant = MockInstant::from_duration(Duration::from_secs(5));
        instant += Duration::from_secs(3);
        assert_eq!(instant.as_duration(), Duration::from_secs(8));
    }

    #[test]
    fn test_sub_duration() {
        let instant = MockInstant::from_duration(Duration::from_secs(10));
        let earlier = instant - Duration::from_secs(3);
        assert_eq!(earlier.as_duration(), Duration::from_secs(7));
    }

    #[test]
    fn test_sub_assign() {
        let mut instant = MockInstant::from_duration(Duration::from_secs(10));
        instant -= Duration::from_secs(3);
        assert_eq!(instant.as_duration(), Duration::from_secs(7));
    }

    #[test]
    fn test_sub_instant() {
        let earlier = MockInstant::from_duration(Duration::from_secs(5));
        let later = MockInstant::from_duration(Duration::from_secs(10));
        assert_eq!(later - earlier, Duration::from_secs(5));
    }

    #[test]
    fn test_ordering() {
        let a = MockInstant::from_duration(Duration::from_secs(5));
        let b = MockInstant::from_duration(Duration::from_secs(10));
        let c = MockInstant::from_duration(Duration::from_secs(5));

        assert!(a < b);
        assert!(b > a);
        assert!(a == c);
        assert!(a <= c);
        assert!(a >= c);
    }

    #[test]
    fn test_from_duration() {
        let instant = MockInstant::from_duration(Duration::from_secs(42));
        assert_eq!(instant.as_duration(), Duration::from_secs(42));
    }
}
