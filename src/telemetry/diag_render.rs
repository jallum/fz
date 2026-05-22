//! Renderer handler that turns telemetry events carrying a `Diagnostic`
//! payload into the same human-readable output `diag::render` produces.
//! The bus routes events to it via prefix `[fz, diag]`; the existing
//! `diag::render::Renderer` does the actual formatting — this type is
//! purely the glue.
//!
//! Both construction paths (stderr and writer) store a `Box<dyn Write>`
//! so `handle` is a single code path with no match arm.

use std::cell::RefCell;
use std::io::Write;
use std::rc::Rc;

use crate::diag::render::Renderer as DiagRenderImpl;
use crate::diag::source_map::SourceMap;
use crate::diag::style::ColorMode;

use super::handler::{Event, Handler};
use super::value::Value;

pub struct DiagRenderer {
    sm: Rc<RefCell<SourceMap>>,
    writer: RefCell<Box<dyn Write>>,
    color: ColorMode,
}

impl DiagRenderer {
    /// Render diagnostic events to stderr with the same color/no-color
    /// policy `diag::render_to_stderr` uses.
    pub fn new_stderr(sm: Rc<RefCell<SourceMap>>) -> Self {
        Self {
            sm,
            writer: RefCell::new(Box::new(std::io::stderr())),
            color: ColorMode::Auto,
        }
    }

    /// Render to an arbitrary writer with the given color mode.
    /// Tests usually pass a `Vec<u8>` and `ColorMode::Never`.
    pub fn new_to_writer<W: Write + 'static>(
        sm: Rc<RefCell<SourceMap>>,
        w: W,
        color: ColorMode,
    ) -> Self {
        Self {
            sm,
            writer: RefCell::new(Box::new(w)),
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
        let mut w = self.writer.borrow_mut();
        let _ = renderer.emit(d, &mut **w);
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
        let buf: Vec<u8> = Vec::new();
        let t = ConfiguredTelemetry::new();
        let shared_buf = Rc::new(RefCell::new(buf));
        {
            let buf_clone = shared_buf.clone();
            t.attach(
                &["fz", "diag"],
                Box::new(DiagRenderer::new_to_writer(
                    sm.clone(),
                    WriterAdaptor(buf_clone),
                    ColorMode::Never,
                )),
            );
        }

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

        let actual = String::from_utf8(shared_buf.borrow().clone()).unwrap();
        let expected = render_to_string(&sm.borrow(), &Diagnostics::from_one(d));
        assert_eq!(actual, expected);
    }

    #[test]
    fn renders_error_identically_to_render_to_string() {
        let (sm, fid) = fixture();
        let buf = Rc::new(RefCell::new(Vec::<u8>::new()));
        let t = ConfiguredTelemetry::new();
        t.attach(
            &["fz", "diag"],
            Box::new(DiagRenderer::new_to_writer(
                sm.clone(),
                WriterAdaptor(buf.clone()),
                ColorMode::Never,
            )),
        );

        let d = Diagnostic::error(DiagCode("test/error"), "test error", Span::new(fid, 3, 7))
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
        let buf = Rc::new(RefCell::new(Vec::<u8>::new()));
        let t = ConfiguredTelemetry::new();
        t.attach(
            &["fz"],
            Box::new(DiagRenderer::new_to_writer(
                sm,
                WriterAdaptor(buf.clone()),
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
        let buf = Rc::new(RefCell::new(Vec::<u8>::new()));
        let t = ConfiguredTelemetry::new();
        t.attach(
            &["fz", "diag"],
            Box::new(DiagRenderer::new_to_writer(
                sm.clone(),
                WriterAdaptor(buf.clone()),
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

    // Adaptor: wraps Rc<RefCell<Vec<u8>>> so it implements Write + 'static,
    // avoiding the Rc<RefCell<dyn Write>> wrapper that the old API needed.
    struct WriterAdaptor(Rc<RefCell<Vec<u8>>>);
    impl Write for WriterAdaptor {
        fn write(&mut self, data: &[u8]) -> std::io::Result<usize> {
            self.0.borrow_mut().extend_from_slice(data);
            Ok(data.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
}
