//! Diagnostics flow through exact raw telemetry callbacks. Printing is the
//! renderer-handler's responsibility.

use super::diagnostic::{Diagnostic, Severity};
use crate::telemetry::{Telemetry, TelemetryExt as _};

/// Emit each diagnostic by reference in the `[fz, diag, *]` family.
pub fn emit_through<T: Telemetry + ?Sized>(tel: &T, diags: &[Diagnostic]) {
    for d in diags {
        let name: &'static [&'static str] = match d.severity {
            Severity::Error => &["fz", "diag", "error"],
            Severity::Warning => &["fz", "diag", "warning"],
        };
        tel.raw_event1(name, d);
    }
}

#[cfg(test)]
#[path = "driver_test.rs"]
mod driver_test;
