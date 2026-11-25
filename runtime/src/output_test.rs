use super::*;
use std::cell::{Cell, RefCell};

struct BorrowCapture {
    pointer: Cell<*const u8>,
    len: Cell<usize>,
}

impl OutputSink for BorrowCapture {
    fn emit(&self, bytes: &[u8]) {
        self.pointer.set(bytes.as_ptr());
        self.len.set(bytes.len());
    }
}

#[test]
fn output_hook_passes_the_original_event_scoped_bytes() {
    let sink = BorrowCapture {
        pointer: Cell::new(std::ptr::null()),
        len: Cell::new(0),
    };
    let context = OutputContext::new(&sink);
    let bytes = b"raw output";

    unsafe { OUTPUT_HOOK(context.as_ptr(), bytes.as_ptr(), bytes.len()) };

    assert_eq!(sink.pointer.get(), bytes.as_ptr());
    assert_eq!(sink.len.get(), bytes.len());
}

struct RetainingCapture(RefCell<Vec<Vec<u8>>>);

impl OutputSink for RetainingCapture {
    fn emit(&self, bytes: &[u8]) {
        self.0.borrow_mut().push(bytes.to_vec());
    }
}

#[test]
fn retaining_sink_owns_its_copy_after_the_callback() {
    let sink = RetainingCapture(RefCell::new(Vec::new()));
    let context = OutputContext::new(&sink);
    {
        let bytes = Vec::from(&b"retained"[..]);
        unsafe { OUTPUT_HOOK(context.as_ptr(), bytes.as_ptr(), bytes.len()) };
    }

    assert_eq!(sink.0.borrow().as_slice(), &[b"retained".to_vec()]);
}

#[test]
fn missing_output_context_does_not_invoke_a_sink() {
    unsafe { OUTPUT_HOOK(std::ptr::null(), b"ignored".as_ptr(), 7) };
}

#[test]
fn null_output_does_not_retain_event_bytes() {
    let context = OutputContext::new(&NullOutput);
    unsafe { OUTPUT_HOOK(context.as_ptr(), b"ignored".as_ptr(), 7) };
}

struct WarningCapture(RefCell<Vec<(String, String, u32)>>);

impl OutputSink for WarningCapture {
    fn emit(&self, _bytes: &[u8]) {}

    fn warn(&self, warning: &Warning<'_>) {
        self.0.borrow_mut().push((
            String::from_utf8_lossy(warning.message).into_owned(),
            String::from_utf8_lossy(warning.file).into_owned(),
            warning.line,
        ));
    }
}

#[test]
fn warn_hook_hands_the_sink_the_message_and_its_location() {
    let sink = WarningCapture(RefCell::new(Vec::new()));
    let context = OutputContext::new(&sink);

    unsafe { WARN_HOOK(context.as_ptr(), b"careful".as_ptr(), 7, b"a.ex".as_ptr(), 4, 3) };
    unsafe { WARN_HOOK(context.as_ptr(), b"bare".as_ptr(), 4, b"".as_ptr(), 0, 0) };

    assert_eq!(
        sink.0.borrow().as_slice(),
        &[
            ("careful".to_string(), "a.ex".to_string(), 3),
            ("bare".to_string(), String::new(), 0),
        ]
    );
}

#[test]
fn a_warning_renders_its_message_and_then_its_location_when_it_has_one() {
    let located = Warning {
        message: b"unused",
        file: b"a.ex",
        line: 3,
    };
    let bare = Warning {
        message: b"unused",
        file: b"",
        line: 0,
    };

    assert_eq!(located.render(), b"warning: unused\n  a.ex:3\n");
    assert_eq!(bare.render(), b"warning: unused\n");
}

#[test]
fn null_output_ignores_warnings_and_a_missing_context_invokes_no_sink() {
    let context = OutputContext::new(&NullOutput);
    unsafe { WARN_HOOK(context.as_ptr(), b"ignored".as_ptr(), 7, b"".as_ptr(), 0, 0) };
    unsafe { WARN_HOOK(std::ptr::null(), b"ignored".as_ptr(), 7, b"".as_ptr(), 0, 0) };
}

struct ExpansionAnswers;

impl OutputSink for ExpansionAnswers {
    fn emit(&self, _bytes: &[u8]) {}

    fn expand(&self, ast: u64, context: i64) -> Expansion {
        match context {
            0 => Expansion::NotAMacro,
            1 => Expansion::Expanded(ast + 8),
            _ => Expansion::Asked,
        }
    }
}

#[test]
fn expand_hook_hands_the_sink_the_call_and_returns_its_answer_with_the_expanded_code() {
    let sink = ExpansionAnswers;
    let context = OutputContext::new(&sink);
    let mut expanded = 0u64;

    let ask = |expansion_context, expanded: &mut u64| unsafe {
        EXPAND_HOOK(context.as_ptr(), 100, expansion_context, expanded)
    };

    assert_eq!(ask(0, &mut expanded), Expansion::NOT_A_MACRO_CODE);
    assert_eq!(ask(1, &mut expanded), Expansion::EXPANDED_CODE);
    assert_eq!(expanded, 108);
    assert_eq!(ask(2, &mut expanded), Expansion::ASKED_CODE);
}

#[test]
fn a_sink_that_does_not_answer_expansions_and_a_missing_context_have_no_compiler() {
    let mut expanded = 0u64;
    let context = OutputContext::new(&NullOutput);
    assert_eq!(
        unsafe { EXPAND_HOOK(context.as_ptr(), 100, 0, &mut expanded) },
        Expansion::NO_COMPILER_CODE
    );
    assert_eq!(
        unsafe { EXPAND_HOOK(std::ptr::null(), 100, 0, &mut expanded) },
        Expansion::NO_COMPILER_CODE
    );
}
