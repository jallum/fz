//! Cooperative yield flag for the fz scheduler.
//!
//! JIT code reads a per-thread flag address captured when the module is
//! built. That keeps independent Rust test harness threads from stealing each
//! other's yield requests while preserving the cheap inline load on every
//! back-edge.
//!
//! `FZ_SHOULD_YIELD` remains exported for AOT-linked code because native
//! Tail-CC fns have no cheap path to the current process and the flag must be
//! reachable via a single known symbol. `set`/`clear` update both the exported
//! symbol and the current thread's JIT flag.
//!
//! The JIT emits a 3-instruction inline check at every back-edge:
//!   load.i8 global_value(%fz_should_yield_data) + 0
//!   brz flag, $fast
//!   ; slow: build continuation closure, call fz_yield_mid_flight, return YIELD_PTR
//!   $fast: return_call callee(args...)

use std::sync::atomic::{AtomicU8, Ordering};

#[unsafe(no_mangle)]
pub static FZ_SHOULD_YIELD: AtomicU8 = AtomicU8::new(0);

thread_local! {
    static THREAD_SHOULD_YIELD: AtomicU8 = const { AtomicU8::new(0) };
}

pub fn request() {
    set(1);
}

pub fn clear() {
    set(0);
}

pub fn set(value: u8) {
    FZ_SHOULD_YIELD.store(value, Ordering::Relaxed);
    THREAD_SHOULD_YIELD.with(|flag| flag.store(value, Ordering::Relaxed));
}

pub fn load() -> u8 {
    THREAD_SHOULD_YIELD.with(|flag| flag.load(Ordering::Relaxed))
}

pub fn jit_flag_ptr() -> *const u8 {
    THREAD_SHOULD_YIELD.with(|flag| flag as *const AtomicU8 as *const u8)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn jit_flag_is_thread_local() {
        clear();
        request();
        assert_eq!(load(), 1);

        std::thread::spawn(|| {
            assert_eq!(load(), 0);
            request();
            assert_eq!(load(), 1);
            clear();
        })
        .join()
        .unwrap();

        assert_eq!(load(), 1);
        clear();
    }
}
