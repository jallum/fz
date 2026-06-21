//! fz-ndf.9 — diagnostics now flow through the telemetry bus:
//! - `report_through(tel, diags)` emits each diagnostic as a
//!   `[fz, diag, error|warning]` event with the `Diagnostic`
//!   in metadata. Printing is the renderer-handler's responsibility.

use super::diagnostic::{Diagnostic, Severity};
use crate::telemetry::Telemetry;
use crate::telemetry::value::opaque;
use crate::telemetry::{Metadata, Value};

/// Emit each diagnostic as a telemetry event in the `[fz, diag, *]`
/// family. Printing is delegated to whatever renderer-handler the bus
/// has attached. No exit decision: callers inspect the slice themselves.
pub fn emit_through(tel: &dyn Telemetry, diags: &[Diagnostic]) {
    for d in diags {
        let (name, severity): (&'static [&'static str], &'static str) = match d.severity {
            Severity::Error => (&["fz", "diag", "error"], "error"),
            Severity::Warning => (&["fz", "diag", "warning"], "warning"),
        };
        let metadata = vec![
            ("severity", Value::from(severity)),
            ("code", Value::from(d.code.0)),
            ("message", Value::from(d.message.as_str())),
            ("diagnostic", opaque(d)),
        ];
        tel.event(name, Metadata::from_pairs(metadata));
    }
}

#[cfg(test)]
#[path = "driver_test.rs"]
mod driver_test;
