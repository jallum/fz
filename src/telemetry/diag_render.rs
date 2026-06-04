//! Renderer handler that turns telemetry events carrying a `Diagnostic`
//! payload into the same human-readable output `diag::render` produces.
//! The bus routes events to it via prefix `[fz, diag]`; the existing
//! `diag::render::Renderer` does the actual formatting — this type is
//! purely the glue.
//!
//! Both construction paths (stderr and writer) store a `Box<dyn Write>`
//! so `handle` is a single code path with no match arm.

use std::cell::RefCell;
use std::io::{Write, stderr};
use std::rc::Rc;

use crate::diag::Diagnostic;
use crate::diag::render::Renderer as DiagRenderImpl;
use crate::diag::source_map::SourceMap;
use crate::diag::style::ColorMode;

use super::handler::{Event, Handler};

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
            writer: RefCell::new(Box::new(stderr())),
            color: ColorMode::Auto,
        }
    }

    /// Render to an arbitrary writer with the given color mode.
    /// Tests usually pass a `Vec<u8>` and `ColorMode::Never`.
    pub fn new_to_writer<W: Write + 'static>(sm: Rc<RefCell<SourceMap>>, w: W, color: ColorMode) -> Self {
        Self {
            sm,
            writer: RefCell::new(Box::new(w)),
            color,
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
        let mut w = self.writer.borrow_mut();
        if let Some(sm) = ev
            .metadata
            .get("source_map")
            .and_then(|v| v.downcast_ref::<SourceMap>())
        {
            let renderer = DiagRenderImpl::new(sm).with_color(self.color);
            let _ = renderer.emit(d, &mut **w);
        } else {
            let sm = self.sm.borrow();
            let renderer = DiagRenderImpl::new(&sm).with_color(self.color);
            let _ = renderer.emit(d, &mut **w);
        }
    }
}

#[cfg(test)]
#[path = "diag_render_test.rs"]
mod diag_render_test;
