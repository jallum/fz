use super::*;
use crate::any_value::{
    AnyValueRef, ClosureDenotationId, ValueKind, closure_addr_from_tagged, closure_capture_set, closure_capture_value,
    map_addr_from_tagged,
};
use crate::exec_ctx::ExecCtx;
use crate::heap::SchemaRegistry;
use crate::process::ClosureRef;
use std::cell::RefCell;
use std::rc::Rc;
use std::slice;

fn with_process<R>(f: impl FnOnce(&mut Process) -> R) -> R {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut process = Box::new(Process::new(schemas));
    // A linked module seeds the reserved atom ids first; this bare process does not.
    for reserved in ["nil", "true", "false"] {
        process.node.intern_atom(reserved);
    }
    f(&mut process)
}

fn atom(process: &Process, name: &str) -> AnyValue {
    AnyValue::atom(process.node.intern_atom(name))
}

fn binary(process: &mut Process, text: &str) -> AnyValue {
    process.heap.alloc_bitstring(text.as_bytes(), 8 * text.len() as u64)
}

fn map(process: &mut Process, entries: &[(&str, AnyValue)]) -> AnyValue {
    let slots: Vec<_> = entries
        .iter()
        .map(|(key, value)| (atom(process, key), *value))
        .collect();
    let bits = process.heap.alloc_map_slots(&slots);
    let addr = map_addr_from_tagged(bits).expect("map addr");
    AnyValue::from_ref(AnyValueRef::from_heap_object(ValueKind::MAP, addr).expect("map ref")).expect("map value")
}

fn exception(process: &mut Process, name: &str, message: &str) -> AnyValue {
    let name = atom(process, name);
    let flag = atom(process, "true");
    let message = binary(process, message);
    map(
        process,
        &[("__struct__", name), ("__exception__", flag), ("message", message)],
    )
}

#[test]
fn an_exception_prints_its_name_and_message() {
    with_process(|process| {
        let value = exception(process, "Elixir.ArgumentError", "bad");
        assert_eq!(failure_line(process, value), "** (ArgumentError) bad");
    });
}

#[test]
fn a_value_that_is_not_an_exception_prints_as_an_erlang_error() {
    with_process(|process| {
        let reason = atom(process, "badarg");
        assert_eq!(failure_line(process, reason), "** (ErlangError) Erlang error: :badarg");
        let text = binary(process, "boom");
        assert_eq!(failure_line(process, text), "** (ErlangError) Erlang error: \"boom\"");
    });
}

#[test]
fn a_struct_shaped_map_without_the_exception_flag_is_not_an_exception() {
    with_process(|process| {
        let name = atom(process, "Elixir.ArgumentError");
        let message = binary(process, "bad");
        let value = map(process, &[("__struct__", name), ("message", message)]);
        let line = failure_line(process, value);
        assert!(
            line.starts_with("** (ErlangError) Erlang error: %{"),
            "only a map flagged __exception__: true names an exception: {line}"
        );
    });
}

unsafe extern "C" fn recording_sink(context: *mut (), line: *const u8, len: usize) {
    let lines = unsafe { &mut *(context as *mut Vec<String>) };
    let line = unsafe { slice::from_raw_parts(line, len) };
    lines.push(String::from_utf8_lossy(line).into_owned());
}

#[test]
fn a_panic_hands_its_line_to_the_fault_sink_marks_the_process_failed_and_returns() {
    with_process(|process| {
        let mut lines: Vec<String> = Vec::new();
        let mut ctx = ExecCtx {
            scheduler: &mut lines as *mut Vec<String> as *mut (),
            fault: Some(recording_sink),
            ..ExecCtx::empty()
        };
        process.ctx = &mut ctx;
        let value = exception(process, "Elixir.RuntimeError", "boom");
        assert!(!process.failed, "a fresh process has not failed");

        fz_panic(process, value.ref_word().raw_word());

        assert!(process.failed, "the panic marks the process failed");
        assert_eq!(
            lines,
            ["** (RuntimeError) boom"],
            "the sink receives exactly one line, without a newline"
        );
    });
}

/// A handler template: `[outer_cont]` with the outer continuation standing in
/// as `nil`, the shape codegen builds before `fz_try_push`.
fn handler_template(process: &mut Process) -> ClosureRef {
    let closure = closure_addr_from_tagged(process.heap.alloc_closure_slots(ClosureDenotationId::INTERNAL, 0, 1, 0))
        .expect("a closure");
    unsafe { closure_capture_set(closure, 0, AnyValue::nil_atom()) };
    ClosureRef::new(AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure).expect("a closure ref"))
}

fn capture(closure: *mut u8, index: usize) -> AnyValue {
    unsafe { closure_capture_value(closure, index) }
}

#[derive(Default)]
struct Observed {
    lines: Vec<String>,
    raises: Vec<(String, String, usize)>,
}

unsafe extern "C" fn observing_sink(context: *mut (), line: *const u8, len: usize) {
    let observed = unsafe { &mut *(context as *mut Observed) };
    let line = unsafe { slice::from_raw_parts(line, len) };
    observed.lines.push(String::from_utf8_lossy(line).into_owned());
}

unsafe extern "C" fn observing_raise(
    context: *mut (),
    kind: *const u8,
    kind_len: usize,
    name: *const u8,
    name_len: usize,
    depth: usize,
) {
    let observed = unsafe { &mut *(context as *mut Observed) };
    let text = |ptr, len| String::from_utf8_lossy(unsafe { slice::from_raw_parts(ptr, len) }).into_owned();
    observed
        .raises
        .push((text(kind, kind_len), text(name, name_len), depth));
}

fn with_observed_process<R>(f: impl FnOnce(&mut Process, &mut Observed) -> R) -> R {
    with_process(|process| {
        let mut observed = Observed::default();
        let mut ctx = ExecCtx {
            scheduler: &mut observed as *mut Observed as *mut (),
            fault: Some(observing_sink),
            raise: Some(observing_raise),
            ..ExecCtx::empty()
        };
        process.ctx = &mut ctx;
        f(process, &mut observed)
    })
}

#[test]
fn a_panic_under_a_compiled_handler_makes_the_handler_runnable_with_kind_value_and_name() {
    with_observed_process(|process, observed| {
        let template = handler_template(process);
        process.push_handler(Handler::Closure(template));
        let value = exception(process, "Elixir.RuntimeError", "boom");

        fz_panic(process, value.ref_word().raw_word());

        assert!(!process.failed, "a caught raise is not a failure");
        assert!(
            process.handlers.is_empty(),
            "the handler is consumed by the raise it catches"
        );
        assert_eq!(process.raises_delivered, 1);
        assert!(observed.lines.is_empty(), "nothing is printed for a caught raise");
        let handler = process
            .runnable_closure()
            .expect("the handler is what runs next")
            .closure_addr()
            .expect("a closure ref");
        assert_ne!(
            handler,
            template.as_ref().closure_addr().expect("a closure ref"),
            "the template itself is untouched"
        );
        assert_eq!(
            capture(handler, 0),
            AnyValue::nil_atom(),
            "the outer continuation comes first"
        );
        assert_eq!(capture(handler, 1), atom(process, "error"));
        assert_eq!(capture(handler, 2), value);
        assert_eq!(capture(handler, 3), atom(process, "Elixir.RuntimeError"));
        assert_eq!(
            observed.raises,
            [("error".to_string(), "Elixir.RuntimeError".to_string(), 1)]
        );
    });
}

#[test]
fn a_panic_under_an_interpreter_handler_leaves_the_raise_for_the_interpreter_to_read() {
    with_observed_process(|process, observed| {
        process.push_handler(Handler::Interpreter);
        let value = atom(process, "boom");
        let value_ref = process.heap.box_any_value_ref(value);

        fz_panic(process, value_ref.raw_word());

        assert!(!process.failed);
        assert!(process.handlers.is_empty());
        assert!(
            process.runnable_closure().is_none(),
            "the interpreter owns its own frames"
        );
        let raised = process.raised.expect("the raise waits in the process");
        assert_eq!(AnyValue::from_ref(raised.kind).expect("kind"), atom(process, "error"));
        assert_eq!(AnyValue::from_ref(raised.value).expect("value"), value);
        assert_eq!(
            AnyValue::from_ref(raised.name).expect("name"),
            AnyValue::nil_atom(),
            "a value that is not an exception has no name"
        );
        assert_eq!(process.raises_delivered, 1);
        assert_eq!(observed.raises, [("error".to_string(), String::new(), 1)]);
    });
}

#[test]
fn a_panic_reaches_the_innermost_handler_and_leaves_the_outer_one_in_place() {
    with_observed_process(|process, observed| {
        let outer = handler_template(process);
        process.push_handler(Handler::Closure(outer));
        process.push_handler(Handler::Interpreter);
        let value = exception(process, "Elixir.KeyError", "key :a not found");

        fz_panic(process, value.ref_word().raw_word());

        assert_eq!(process.handlers, [Handler::Closure(outer)]);
        assert!(
            process.raised.is_some(),
            "the interpreter marker, innermost, took the raise"
        );
        assert_eq!(
            observed.raises,
            [("error".to_string(), "Elixir.KeyError".to_string(), 2)]
        );
    });
}

#[test]
fn a_panic_without_a_handler_is_reported_at_depth_zero_and_still_fails_the_process() {
    with_observed_process(|process, observed| {
        let value = exception(process, "Elixir.RuntimeError", "boom");

        fz_panic(process, value.ref_word().raw_word());

        assert!(process.failed);
        assert_eq!(process.raises_delivered, 0);
        assert_eq!(observed.lines, ["** (RuntimeError) boom"]);
        assert_eq!(
            observed.raises,
            [("error".to_string(), "Elixir.RuntimeError".to_string(), 0)]
        );
    });
}

#[test]
fn a_panic_reports_nothing_when_the_context_does_not_observe_raises() {
    with_process(|process| {
        let mut lines: Vec<String> = Vec::new();
        let mut ctx = ExecCtx {
            scheduler: &mut lines as *mut Vec<String> as *mut (),
            fault: Some(recording_sink),
            ..ExecCtx::empty()
        };
        process.ctx = &mut ctx;
        process.push_handler(Handler::Interpreter);
        let value = atom(process, "boom");
        let value_ref = process.heap.box_any_value_ref(value);

        fz_panic(process, value_ref.raw_word());

        assert!(process.raised.is_some());
        assert!(lines.is_empty());
    });
}

/// Runs `f` on a process whose fault sink records lines; answers the lines
/// and whether the process failed.
fn recording(f: impl FnOnce(&mut Process)) -> (Vec<String>, bool) {
    with_process(|process| {
        let mut lines: Vec<String> = Vec::new();
        let mut ctx = ExecCtx {
            scheduler: &mut lines as *mut Vec<String> as *mut (),
            fault: Some(recording_sink),
            ..ExecCtx::empty()
        };
        process.ctx = &mut ctx;
        f(process);
        process.ctx = std::ptr::null_mut();
        (lines, process.failed)
    })
}

#[test]
fn a_raise_panics_with_the_exception_elixir_raises() {
    let (lines, failed) = recording(|process| {
        let name = atom(process, "Elixir.CondClauseError");
        raise_exception(process, name, "no cond clause evaluated to a truthy value");
    });
    assert!(failed, "a raise fails the process through the panic route");
    assert_eq!(
        lines,
        ["** (CondClauseError) no cond clause evaluated to a truthy value"],
        "the exception prints as Elixir prints it"
    );
}

#[test]
fn a_message_about_a_term_sets_the_term_on_its_own_indented_line() {
    with_process(|process| {
        assert_eq!(
            message_showing(process, "no case clause matching:", AnyValue::Int(3)),
            "no case clause matching:\n\n    3\n",
            "Elixir 1.19 words CaseClauseError's message this way"
        );
    });
}

#[test]
fn the_raise_exports_take_value_words_and_reach_the_same_route() {
    let (lines, failed) = recording(|process| {
        let name = atom(process, "Elixir.MatchError");
        let name = process.heap.box_any_value_ref(name).raw_word();
        let lead = binary(process, "no match of right hand side value:");
        let term = process.heap.box_any_value_ref(AnyValue::Int(7)).raw_word();
        fz_raise_showing(process, name, lead.ref_word().raw_word(), term);
    });
    assert!(failed);
    assert_eq!(lines, ["** (MatchError) no match of right hand side value:\n\n    7\n"]);
}

#[test]
fn a_plain_raise_export_carries_its_message_unchanged() {
    let (lines, failed) = recording(|process| {
        let name = atom(process, "Elixir.ArgumentError");
        let name = process.heap.box_any_value_ref(name).raw_word();
        let message = binary(process, "argument error");
        fz_raise(process, name, message.ref_word().raw_word());
    });
    assert!(failed);
    assert_eq!(lines, ["** (ArgumentError) argument error"]);
}
