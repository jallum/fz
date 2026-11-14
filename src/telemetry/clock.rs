//! The nanosecond readings spans and event lines carry.
//!
//! A [`Clock`] is the one place telemetry reads time. The system clock counts
//! from the moment it was made; a ticking clock (tests only) advances one
//! nanosecond per reading, so a test that needs time to have passed between
//! two readings reads the clock twice instead of waiting.

use std::sync::OnceLock;
use std::time::Instant;

pub struct Clock {
    reading: Box<dyn Fn() -> u64>,
}

impl Clock {
    /// Nanoseconds since this clock was made, on the monotonic system clock.
    pub fn system() -> Self {
        let began = Instant::now();
        Self {
            reading: Box::new(move || saturating_nanos(began)),
        }
    }

    /// A clock whose every reading is one nanosecond later than the last.
    #[cfg(test)]
    pub fn ticking() -> Self {
        let ticks = std::cell::Cell::new(0_u64);
        Self {
            reading: Box::new(move || {
                ticks.set(ticks.get() + 1);
                ticks.get()
            }),
        }
    }

    pub fn now_ns(&self) -> u64 {
        (self.reading)()
    }
}

/// Nanoseconds on the process-wide monotonic clock, for a [`Telemetry`]
/// that keeps no clock of its own.
///
/// [`Telemetry`]: super::Telemetry
pub fn system_now_ns() -> u64 {
    static BEGAN: OnceLock<Instant> = OnceLock::new();
    saturating_nanos(*BEGAN.get_or_init(Instant::now))
}

fn saturating_nanos(began: Instant) -> u64 {
    began.elapsed().as_nanos().min(u64::MAX as u128) as u64
}
