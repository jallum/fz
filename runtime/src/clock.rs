//! The scheduler's one source of time, and its one way of waiting for it.
//!
//! A [`Clock`] answers "what time is it?" and "wait this long". The system
//! clock reads the monotonic system clock and sleeps the thread. A manual clock
//! (tests only) keeps its own time and waiting advances it, so a test that
//! drives the scheduling core past a deadline neither sleeps nor races.

use std::time::{Duration, Instant};

/// Time as a scheduler sees it. `epoch` is the instant the clock began;
/// deadlines are reported as a [`Duration`] since it.
pub struct Clock {
    epoch: Instant,
    source: Source,
}

enum Source {
    System,
    #[cfg(test)]
    Manual(Duration),
}

impl Default for Clock {
    fn default() -> Self {
        Self::system()
    }
}

impl Clock {
    /// The monotonic system clock; waiting sleeps the thread.
    pub fn system() -> Self {
        Self {
            epoch: Instant::now(),
            source: Source::System,
        }
    }

    /// A clock that starts now and moves only when something waits on it.
    #[cfg(test)]
    pub fn manual() -> Self {
        Self {
            epoch: Instant::now(),
            source: Source::Manual(Duration::ZERO),
        }
    }

    pub fn now(&self) -> Instant {
        match self.source {
            Source::System => Instant::now(),
            #[cfg(test)]
            Source::Manual(elapsed) => self.epoch + elapsed,
        }
    }

    /// How long after the clock began `instant` falls.
    pub fn since_epoch(&self, instant: Instant) -> Duration {
        instant.saturating_duration_since(self.epoch)
    }

    /// Wait `wait`: sleep for it, or, on a manual clock, let it pass.
    pub fn wait(&mut self, wait: Duration) {
        match &mut self.source {
            Source::System => std::thread::sleep(wait),
            #[cfg(test)]
            Source::Manual(elapsed) => *elapsed += wait,
        }
    }
}
