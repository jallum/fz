//! fz-ndf.9 — diagnostics now flow through the telemetry bus:
//! - `report_through(tel, diags)` emits each diagnostic as a
//!   `[fz, diag, error|warning]` event with the `Diagnostic`
//!   in metadata. Printing is the renderer-handler's responsibility.

use super::diagnostic::{Diagnostic, Severity};
use super::render::Renderer;
use super::source_map::SourceMap;
use crate::telemetry::Telemetry;
use crate::telemetry::value::opaque;
use crate::telemetry::{Metadata, Value};
use std::process::exit;

/// Render one diagnostic into a deterministic, color-free string.
pub fn render_one_to_string(sm: &SourceMap, d: &Diagnostic) -> String {
    let renderer = Renderer::new(sm).with_color_disabled();
    let mut out = Vec::new();
    let _ = renderer.emit(d, &mut out);
    String::from_utf8(out).unwrap_or_else(|e| String::from_utf8_lossy(e.as_bytes()).into_owned())
}

/// Emit each diagnostic as a telemetry event in the `[fz, diag, *]`
/// family. Printing is delegated to whatever renderer-handler the bus
/// has attached (typically `DiagRenderer`). No exit decision — callers
/// inspect the slice themselves or use `report_or_exit_through` which
/// combines emission with exit-on-error.
pub fn emit_through(tel: &dyn Telemetry, sm: Option<&SourceMap>, diags: &[Diagnostic]) {
    for d in diags {
        let (name, severity): (&'static [&'static str], &'static str) = match d.severity {
            Severity::Error => (&["fz", "diag", "error"], "error"),
            Severity::Warning => (&["fz", "diag", "warning"], "warning"),
        };
        let mut metadata = vec![
            ("severity", Value::from(severity)),
            ("code", Value::from(d.code.0)),
            ("message", Value::from(d.message.as_str())),
            ("diagnostic", opaque(d)),
        ];
        if let Some(sm) = sm {
            metadata.push(("source_map", opaque(sm)));
        }
        tel.event(name, Metadata::from_pairs(metadata));
    }
}

/// Same emission shape as `report_or_exit`, but the caller supplies the
/// telemetry. Use this from any code path that has already constructed
/// a bus (e.g. a long-lived driver bus); it skips the one-shot
/// construction and exits on error severity.
pub fn report_or_exit_through(tel: &dyn Telemetry, diags: &[Diagnostic]) {
    if diags.is_empty() {
        return;
    }
    emit_through(tel, None, diags);
    if diags.iter().any(|d| d.severity == Severity::Error) {
        exit(1);
    }
}

#[cfg(test)]
#[path = "driver_test.rs"]
mod driver_test;
