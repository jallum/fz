//! Renderer handler that turns telemetry events carrying a `Diagnostic`
//! payload into the same human-readable output `diag::render` produces.
//! The bus routes events to it via prefix `[fz, diag]`; the existing
//! `diag::render::Renderer` does the actual formatting — this type is
//! purely the glue.
//!
//! Construction stores a `Box<dyn Write>` so `handle` is a single code path
//! with no match arm.

use std::cell::{Cell, RefCell};
use std::io::Write;
use std::rc::Rc;

use crate::diag::Diagnostic;
use crate::diag::render::Renderer as DiagRenderImpl;
use crate::diag::style::ColorMode;
use crate::source::SourceMap;

use super::handler::{Event, Handler};

pub struct DiagRenderer {
    fallback_source_map: Option<Rc<RefCell<SourceMap>>>,
    writer: RefCell<Box<dyn Write>>,
    color: ColorMode,
    saw_error: Rc<Cell<bool>>,
}

#[derive(Clone)]
pub struct DiagnosticStatus {
    saw_error: Rc<Cell<bool>>,
}

impl DiagnosticStatus {
    pub fn new() -> Self {
        Self {
            saw_error: Rc::new(Cell::new(false)),
        }
    }

    pub fn saw_error(&self) -> bool {
        self.saw_error.get()
    }
}

impl DiagRenderer {
    /// Render to an arbitrary writer with the given color mode.
    /// Tests usually pass a `Vec<u8>` and `ColorMode::Never`.
    #[cfg(test)]
    pub fn new_to_writer<W: Write + 'static>(sm: Rc<RefCell<SourceMap>>, w: W, color: ColorMode) -> Self {
        Self {
            fallback_source_map: Some(sm),
            writer: RefCell::new(Box::new(w)),
            color,
            saw_error: Rc::new(Cell::new(false)),
        }
    }

    pub fn new_to_stderr_with_status(sm: Rc<RefCell<SourceMap>>, color: ColorMode, status: DiagnosticStatus) -> Self {
        Self {
            fallback_source_map: Some(sm),
            writer: RefCell::new(Box::new(std::io::stderr())),
            color,
            saw_error: status.saw_error,
        }
    }
}

impl Handler for DiagRenderer {
    fn handle(&self, ev: &Event<'_, '_, '_>) {
        let Some(d) = ev
            .metadata
            .get("diagnostic")
            .and_then(|v| v.downcast_ref::<Diagnostic>())
        else {
            return;
        };
        if matches!(d.severity, crate::diag::diagnostic::Severity::Error) {
            self.saw_error.set(true);
        }
        let mut w = self.writer.borrow_mut();
        if let Some(sm) = &self.fallback_source_map {
            let sm = sm.borrow();
            let renderer = DiagRenderImpl::new(&sm).with_color(self.color);
            let _ = renderer.emit(d, &mut **w);
        }
    }
}

#[cfg(test)]
#[path = "diag_render_test.rs"]
mod diag_render_test;
