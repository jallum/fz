//! What a macro run answers beyond its value: the warnings its body emitted
//! with `IO.warn`, in the order it emitted them.
//!
//! The expansion and its warnings travel together, so a memoized expansion
//! reports the same warnings as the run that produced it.

use std::cell::RefCell;

use fz_runtime::output::{OutputSink, STDOUT_OUTPUT, Warning};

use crate::diag::{Diagnostic, codes};
use crate::source::{SourceMap, Span};

use super::source::QuotedSourceRoot;

/// One `IO.warn` a macro body ran: its message, and the file and line it
/// names when it names any.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MacroWarning {
    message: String,
    location: Option<WarnedLocation>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct WarnedLocation {
    file: String,
    line: u32,
}

/// A macro's result and every warning its run emitted.
#[derive(Clone)]
pub(crate) struct MacroExpansion {
    pub(crate) root: QuotedSourceRoot,
    pub(crate) warnings: Vec<MacroWarning>,
}

/// The output of a macro run: a print goes to stdout as it does in a program,
/// and a warning is kept for the compiler to report.
#[derive(Default)]
pub(crate) struct MacroRunOutput {
    warnings: RefCell<Vec<MacroWarning>>,
}

impl MacroRunOutput {
    pub(crate) fn into_warnings(self) -> Vec<MacroWarning> {
        self.warnings.into_inner()
    }
}

impl OutputSink for MacroRunOutput {
    fn emit(&self, bytes: &[u8]) {
        STDOUT_OUTPUT.emit(bytes);
    }

    fn warn(&self, warning: &Warning<'_>) {
        let location = (!warning.file.is_empty()).then(|| WarnedLocation {
            file: String::from_utf8_lossy(warning.file).into_owned(),
            line: warning.line,
        });
        self.warnings.borrow_mut().push(MacroWarning {
            message: String::from_utf8_lossy(warning.message).into_owned(),
            location,
        });
    }

    fn flush(&self) {
        STDOUT_OUTPUT.flush();
    }
}

impl MacroWarning {
    /// The warning as the compiler reports it. It points at the macro's call
    /// unless it names a line of the call's own file, and then at that line.
    /// A file the compiler has no source for is named in a note, since a
    /// diagnostic can only point into source it holds.
    pub(crate) fn diagnostic(&self, call: Option<Span>, source_map: &SourceMap) -> Diagnostic {
        let call = call.filter(|span| !span.is_dummy());
        let Some(location) = &self.location else {
            return self.pointing_at(call);
        };
        let Some(call_span) = call else {
            return self.pointing_at(call).with_note(location.note());
        };
        let called_file = source_map.name(call_span.source_version);
        if called_file != Some(location.file.as_str()) {
            return self.pointing_at(call).with_note(location.note());
        }
        if source_map.locate(call_span).line == location.line {
            return self.pointing_at(call);
        }
        match source_map.line_span(call_span.source_version, location.line) {
            Some(line) => self.pointing_at(Some(line)),
            None => self.pointing_at(call).with_note(location.note()),
        }
    }

    fn pointing_at(&self, span: Option<Span>) -> Diagnostic {
        Diagnostic::warning(codes::MACRO_WARNING, self.message.clone(), span.unwrap_or(Span::DUMMY))
    }
}

impl WarnedLocation {
    fn note(&self) -> String {
        format!("warned at {}:{}", self.file, self.line)
    }
}

#[cfg(test)]
#[path = "macro_warning_test.rs"]
mod macro_warning_test;
