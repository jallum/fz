//! Event-count aggregator for the telemetry bus (fz-ndf.13).
//!
//! `StatsHandler` counts every event by its full name (joined with `.`).
//! Callers retain an `Rc<StatsHandler>` clone (same pattern as `Capture`)
//! to call `print_summary()` after the compilation run, or to inspect
//! counts in tests.
//!
//! Only `EventKind::Event` ticks are counted; span start/stop events are
//! filtered out so the summary reflects user-visible pipeline events, not
//! span bookkeeping.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use super::handler::{Event, Handler};

struct Inner {
    counts: BTreeMap<String, u64>,
}

pub struct StatsHandler {
    inner: Rc<RefCell<Inner>>,
}

impl StatsHandler {
    pub fn new() -> Self {
        Self {
            inner: Rc::new(RefCell::new(Inner {
                counts: BTreeMap::new(),
            })),
        }
    }

    /// Returns a boxed `Handler` that shares the same counters. Attach this
    /// to the bus; keep `self` to query or print after the run.
    pub fn handler(&self) -> Box<dyn Handler> {
        Box::new(SharedStats {
            inner: self.inner.clone(),
        })
    }

    /// Copy of the current event counts, keyed by `.`-joined name.
    #[cfg(test)]
    pub fn counts(&self) -> BTreeMap<String, u64> {
        self.inner.borrow().counts.clone()
    }

    /// Total events recorded (sum of all counters).
    #[cfg(test)]
    pub fn total(&self) -> u64 {
        self.inner.borrow().counts.values().sum()
    }

    /// Print a summary table to stderr. Rows are sorted alphabetically by
    /// event name. Empty if no events were seen.
    pub fn print_summary(&self) {
        let inner = self.inner.borrow();
        if inner.counts.is_empty() {
            return;
        }
        eprintln!("telemetry stats:");
        for (name, count) in &inner.counts {
            eprintln!("  {:48} {}", name, count);
        }
    }
}

struct SharedStats {
    inner: Rc<RefCell<Inner>>,
}

impl Handler for SharedStats {
    fn handle(&self, ev: &Event<'_, '_, '_>) {
        if ev.kind.is_span() {
            return;
        }
        let key = ev.name.join(".");
        let mut inner = self.inner.borrow_mut();
        *inner.counts.entry(key).or_insert(0) += 1;
    }
}

#[cfg(test)]
#[path = "stats_test.rs"]
mod stats_test;
