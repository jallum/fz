//! ANSI escape helpers and TTY/NO_COLOR detection (fz-ul4.20.6).
//!
//! Tiny by design — no `crossterm` / `termcolor` dependency. Honors the
//! NO_COLOR convention (https://no-color.org) and IsTerminal probing
//! from the Rust 2024 edition's stable surface.

use std::env::var_os;
use std::io::{IsTerminal, stderr};

use ColorMode::{Auto, Never};

pub const RESET: &str = "\x1b[0m";
pub const BOLD: &str = "\x1b[1m";
pub const RED: &str = "\x1b[31m";
pub const YELLOW: &str = "\x1b[33m";
pub const CYAN: &str = "\x1b[36m";
pub const GREEN: &str = "\x1b[32m";
pub const BLUE: &str = "\x1b[34m";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ColorMode {
    Auto,
    Never,
}

impl ColorMode {
    /// Resolve `Auto` against the destination stream and `NO_COLOR`.
    /// `Never` is honored verbatim.
    pub fn use_color(self, stream_is_terminal: bool) -> bool {
        match self {
            Never => false,
            Auto => {
                if var_os("NO_COLOR").is_some() {
                    return false;
                }
                stream_is_terminal
            }
        }
    }
}

/// Convenience: pull color decision from a writer if it can detect TTY-ness.
/// Falls back to `Never` when the writer doesn't expose `IsTerminal` (we
/// only check stderr / stdout in practice).
pub fn use_color_for_stderr(mode: ColorMode) -> bool {
    mode.use_color(stderr().is_terminal())
}

#[cfg(test)]
mod tests {
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
}
