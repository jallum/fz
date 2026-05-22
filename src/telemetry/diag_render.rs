//! Renderer handler that turns telemetry events carrying a `Diagnostic`
//! payload into the same human-readable output `diag::render` produces
//! today. The bus routes events to it via prefix `[fz, diag]`; the
//! existing `diag::render::Renderer` does the actual formatting — this
//! type is purely the glue.

use std::cell::RefCell;
use std::io::Write;
use std::rc::Rc;

use crate::diag::render::Renderer as DiagRenderImpl;
use crate::diag::source_map::SourceMap;
use crate::diag::style::ColorMode;

use super::handler::{Event, Handler};
use super::value::Value;

/// Output sink for the diagnostic renderer.
pub enum DiagOutput {
    /// Locks and writes to `std::io::stderr()` on each event.
    Stderr,
    /// Shared writer (typically a `Vec<u8>` in tests).
    Writer(Rc<RefCell<dyn Write + 'static>>),
}

pub struct DiagRenderer {
    sm: Rc<RefCell<SourceMap>>,
    output: DiagOutput,
    color: ColorMode,
}

impl DiagRenderer {
    /// Render diagnostic events to stderr with the same color/no-color
    /// policy `diag::render_to_stderr` uses.
    pub fn new_stderr(sm: Rc<RefCell<SourceMap>>) -> Self {
        Self {
            sm,
            output: DiagOutput::Stderr,
            color: ColorMode::Auto,
        }
    }

    /// Render to a shared buffer with the given color mode. Tests usually
    /// pass `ColorMode::Never` and an `Rc<RefCell<Vec<u8>>>`.
    pub fn new_to_writer<W: Write + 'static>(
        sm: Rc<RefCell<SourceMap>>,
        w: Rc<RefCell<W>>,
        color: ColorMode,
    ) -> Self {
        Self {
            sm,
            output: DiagOutput::Writer(w),
            color,
        }
    }
}

impl Handler for DiagRenderer {
    fn handle(&self, ev: &Event<'_>) {
        let Some(Value::Diagnostic(d)) = ev.metadata.get("diagnostic") else {
            return;
        };
        let sm = self.sm.borrow();
        let renderer = DiagRenderImpl::new(&sm).with_color(self.color);
        match &self.output {
            DiagOutput::Stderr => {
                let mut w = std::io::stderr().lock();
                let _ = renderer.emit(d, &mut w);
            }
            DiagOutput::Writer(w) => {
                let mut w = w.borrow_mut();
                // diag::render::Renderer::emit takes `impl Write` (Sized);
                // wrap the unsized dyn ref in a sized `&mut &mut dyn Write`.
                let mut dyn_w: &mut dyn Write = &mut *w;
                let _ = renderer.emit(d, &mut dyn_w);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::diagnostic::{DiagCode, Diagnostic, Diagnostics};
    use crate::diag::driver::render_to_string;
    use crate::diag::span::Span;
    use crate::metadata;
    use crate::telemetry::bus::ConfiguredTelemetry;
    use crate::telemetry::event::{Measurements, Metadata};
    use crate::telemetry::sink::Telemetry;

    fn fixture() -> (Rc<RefCell<SourceMap>>, crate::diag::span::FileId) {
        let mut sm = SourceMap::new();
        let fid = sm.add_file("test.fz", "fn main(), do: :ok\n");
        (Rc::new(RefCell::new(sm)), fid)
    }

    #[test]
    fn renders_warning_identically_to_render_to_string() {
        let (sm, fid) = fixture();
        let buf: Rc<RefCell<Vec<u8>>> = Rc::new(RefCell::new(Vec::new()));
        let t = ConfiguredTelemetry::new();
        t.attach(
            &["fz", "diag"],
            Box::new(DiagRenderer::new_to_writer(
                sm.clone(),
                buf.clone(),
                ColorMode::Never,
            )),
        );

        let d = Diagnostic::warning(
            DiagCode("test/warning"),
            "test warning",
            Span::new(fid, 0, 2),
        )
        .with_label("here");

        t.execute(
            &["fz", "diag", "warning"],
            &Measurements::new(),
            &metadata! { diagnostic: d.clone() },
        );

        let actual = String::from_utf8(buf.borrow().clone()).unwrap();
        let expected = render_to_string(&sm.borrow(), &Diagnostics::from_one(d));
        assert_eq!(actual, expected);
    }

    #[test]
    fn renders_error_identically_to_render_to_string() {
        let (sm, fid) = fixture();
        let buf: Rc<RefCell<Vec<u8>>> = Rc::new(RefCell::new(Vec::new()));
        let t = ConfiguredTelemetry::new();
        t.attach(
            &["fz", "diag"],
            Box::new(DiagRenderer::new_to_writer(
                sm.clone(),
                buf.clone(),
                ColorMode::Never,
            )),
        );

        let d = Diagnostic::error(
            DiagCode("test/error"),
            "test error",
            Span::new(fid, 3, 7),
        )
        .with_note("first note")
        .with_help("did you mean foo?");

        t.execute(
            &["fz", "diag", "error"],
            &Measurements::new(),
            &metadata! { diagnostic: d.clone() },
        );

        let actual = String::from_utf8(buf.borrow().clone()).unwrap();
        let expected = render_to_string(&sm.borrow(), &Diagnostics::from_one(d));
        assert_eq!(actual, expected);
    }

    #[test]
    fn ignores_events_without_diagnostic_metadata() {
        let (sm, _fid) = fixture();
        let buf: Rc<RefCell<Vec<u8>>> = Rc::new(RefCell::new(Vec::new()));
        let t = ConfiguredTelemetry::new();
        t.attach(
            &["fz"],
            Box::new(DiagRenderer::new_to_writer(
                sm,
                buf.clone(),
                ColorMode::Never,
            )),
        );
        t.execute(
            &["fz", "lex", "tokens_built"],
            &Measurements::new(),
            &Metadata::new(),
        );
        assert!(buf.borrow().is_empty());
    }

    #[test]
    fn multiple_diagnostics_concatenate_in_order() {
        let (sm, fid) = fixture();
        let buf: Rc<RefCell<Vec<u8>>> = Rc::new(RefCell::new(Vec::new()));
        let t = ConfiguredTelemetry::new();
        t.attach(
            &["fz", "diag"],
            Box::new(DiagRenderer::new_to_writer(
                sm.clone(),
                buf.clone(),
                ColorMode::Never,
            )),
        );

        let d1 = Diagnostic::warning(DiagCode("a/1"), "first", Span::new(fid, 0, 1));
        let d2 = Diagnostic::error(DiagCode("a/2"), "second", Span::new(fid, 2, 3));

        t.execute(
            &["fz", "diag", "warning"],
            &Measurements::new(),
            &metadata! { diagnostic: d1.clone() },
        );
        t.execute(
            &["fz", "diag", "error"],
            &Measurements::new(),
            &metadata! { diagnostic: d2.clone() },
        );

        let mut ds = Diagnostics::new();
        ds.push(d1);
        ds.push(d2);
        let expected = render_to_string(&sm.borrow(), &ds);
        let actual = String::from_utf8(buf.borrow().clone()).unwrap();
        assert_eq!(actual, expected);
    }
}
