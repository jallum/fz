use super::*;
use std::env::{remove_var, set_var};

#[test]
fn never_returns_false_regardless() {
    assert!(!Never.use_color(true));
    assert!(!Never.use_color(false));
}

#[test]
fn auto_respects_tty_signal() {
    // Without NO_COLOR set, Auto follows the stream.
    // Sanity: tests may run with NO_COLOR set in CI — keep this lenient.
    if var_os("NO_COLOR").is_none() {
        assert!(!Auto.use_color(false));
        assert!(Auto.use_color(true));
    }
}

#[test]
fn no_color_forces_off_even_on_tty() {
    // SAFETY: env mutation in tests is dicey; we save and restore.
    let prev = var_os("NO_COLOR");
    unsafe {
        set_var("NO_COLOR", "1");
    }
    let result = Auto.use_color(true);
    match prev {
        Some(v) => unsafe {
            set_var("NO_COLOR", v);
        },
        None => unsafe {
            remove_var("NO_COLOR");
        },
    }
    assert!(!result, "NO_COLOR should force Auto off");
}
