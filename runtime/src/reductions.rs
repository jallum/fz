//! Thread-local reduction budget and yield-reason cells.
//!
//! The interpreter spends the thread-local budget directly. Runtime allocation
//! pressure expires it and records reason bits that are merged into the next
//! scheduler yield report.

use std::sync::atomic::AtomicU8;
use std::sync::atomic::{AtomicI32, Ordering};

use crate::process::DEFAULT_REDUCTIONS_PER_QUANTUM;

thread_local! {
    static THREAD_REDUCTIONS_REMAINING: AtomicI32 =
        const { AtomicI32::new(DEFAULT_REDUCTIONS_PER_QUANTUM) };
    static THREAD_YIELD_REASONS: AtomicU8 = const { AtomicU8::new(0) };
}

pub fn install_budget(value: i32) {
    THREAD_REDUCTIONS_REMAINING.with(|cell| cell.store(value, Ordering::Relaxed));
    clear_yield_reasons();
}

pub fn load() -> i32 {
    THREAD_REDUCTIONS_REMAINING.with(|cell| cell.load(Ordering::Relaxed))
}

pub fn expire_for(reason: u8) {
    if let Some(process) = crate::process::try_current_process() {
        process.reductions_remaining = 0;
    }
    THREAD_REDUCTIONS_REMAINING.with(|cell| cell.store(0, Ordering::Relaxed));
    THREAD_YIELD_REASONS.with(|cell| {
        cell.fetch_or(reason, Ordering::Relaxed);
    });
}

pub fn take_yield_reasons() -> u8 {
    THREAD_YIELD_REASONS.with(|cell| cell.swap(0, Ordering::Relaxed))
}

pub fn clear_yield_reasons() {
    THREAD_YIELD_REASONS.with(|cell| cell.store(0, Ordering::Relaxed));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn budget_cell_is_thread_local() {
        install_budget(7);
        assert_eq!(load(), 7);

        std::thread::spawn(|| {
            assert_eq!(load(), DEFAULT_REDUCTIONS_PER_QUANTUM);
            install_budget(3);
            assert_eq!(load(), 3);
        })
        .join()
        .unwrap();

        assert_eq!(load(), 7);
    }

    #[test]
    fn expire_for_records_reason_and_clears_on_take() {
        install_budget(7);
        expire_for(crate::process::YIELD_REASON_ALLOCATION_PRESSURE);

        assert_eq!(load(), 0);
        assert_eq!(
            take_yield_reasons(),
            crate::process::YIELD_REASON_ALLOCATION_PRESSURE
        );
        assert_eq!(take_yield_reasons(), 0);
    }

    #[test]
    fn expire_for_zeros_installed_process_budget() {
        let schemas = std::rc::Rc::new(std::cell::RefCell::new(crate::heap::SchemaRegistry::new()));
        let mut process = crate::process::Process::new(schemas);
        process.reductions_remaining = 7;
        let _guard = crate::process::CurrentProcessGuard::install(&mut process);

        expire_for(crate::process::YIELD_REASON_ALLOCATION_PRESSURE);

        assert_eq!(process.reductions_remaining, 0);
    }
}
