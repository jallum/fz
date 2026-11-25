//! What a macro run answers beyond its value, and what it asks along the way.
//!
//! A run answers the warnings its body emitted with `IO.warn`, in the order it
//! emitted them, and what it printed. The expansion and its warnings travel
//! together, so a memoized expansion reports the same warnings as the run that
//! produced it.
//!
//! A run asks the compiler to expand a macro call (`Macro.expand/2`): the body
//! has no handle to the world, and the answer may have to wait for a fact. The
//! first question the run has no answer for stops it: the compiler answers
//! that question and runs the body again with every answer so far in hand. A
//! body is a pure function of its arguments and those answers, so each run
//! asks the same questions in the same order, and a run that asked is
//! discarded, its warnings and its prints with it.

use std::cell::{Cell, RefCell};

use fz_runtime::any_value::AnyValueRef;
use fz_runtime::output::{Expansion, OutputSink, STDOUT_OUTPUT, Warning};

use crate::diag::{Diagnostic, codes};
use crate::source::{SourceMap, Span};

use super::quoted_expander::ExpansionContext;
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

/// A macro's result and every warning its run emitted, with how many
/// expansion numbers the run's questions drew, so that reusing the expansion
/// leaves the job's numbering where running it would.
#[derive(Clone)]
pub(crate) struct MacroExpansion {
    pub(crate) root: QuotedSourceRoot,
    pub(crate) warnings: Vec<MacroWarning>,
    pub(crate) answered_expansions: i64,
}

/// A macro body's question: what is this macro call after one step, standing
/// in `context`?
#[derive(Clone, Copy, Debug)]
pub(crate) struct ExpansionRequest {
    pub(crate) call: AnyValueRef,
    pub(crate) context: ExpansionContext,
}

/// What the compiler answered a request.
#[derive(Clone, Copy, Debug)]
pub(crate) enum ExpansionAnswer {
    NotAMacro,
    Expanded(AnyValueRef),
}

/// How a macro run ended.
pub(crate) enum MacroRun {
    Finished {
        root: QuotedSourceRoot,
        warnings: Vec<MacroWarning>,
    },
    /// The run stopped at a question it had no answer for.
    Asked(ExpansionRequest),
}

/// The output of a macro run: what it prints is kept until the run is known
/// to be the last, a warning is kept for the compiler to report, and a request
/// to expand a macro call is answered from `answers` in the order asked.
#[derive(Default)]
pub(crate) struct MacroRunOutput {
    printed: RefCell<Vec<u8>>,
    warnings: RefCell<Vec<MacroWarning>>,
    answers: Vec<ExpansionAnswer>,
    answered: Cell<usize>,
    asked: RefCell<Option<ExpansionRequest>>,
}

impl MacroRunOutput {
    /// The output of a run that already has `answers` to its first questions.
    pub(crate) fn answering(answers: &[ExpansionAnswer]) -> Self {
        Self {
            answers: answers.to_vec(),
            ..Self::default()
        }
    }

    pub(crate) fn into_warnings(self) -> Vec<MacroWarning> {
        self.warnings.into_inner()
    }

    /// The question the run stopped at, if it did.
    pub(crate) fn asked(&self) -> Option<ExpansionRequest> {
        *self.asked.borrow()
    }

    /// Hands what the run printed to standard output, as a program's prints
    /// are.
    pub(crate) fn print(&self) {
        STDOUT_OUTPUT.emit(&self.printed.borrow());
        STDOUT_OUTPUT.flush();
    }
}

impl OutputSink for MacroRunOutput {
    fn emit(&self, bytes: &[u8]) {
        self.printed.borrow_mut().extend_from_slice(bytes);
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

    fn expand(&self, call: u64, context: i64) -> Expansion {
        let answered = self.answered.get();
        if let Some(answer) = self.answers.get(answered) {
            self.answered.set(answered + 1);
            return match answer {
                ExpansionAnswer::NotAMacro => Expansion::NotAMacro,
                ExpansionAnswer::Expanded(root) => Expansion::Expanded(root.raw_word()),
            };
        }
        self.asked.borrow_mut().get_or_insert_with(|| ExpansionRequest {
            call: AnyValueRef::from_raw_word(call).expect("a macro body asks about a quoted value"),
            context: ExpansionContext::from_code(context),
        });
        Expansion::Asked
    }

    fn flush(&self) {}
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
#[path = "macro_run_test.rs"]
mod macro_run_test;
