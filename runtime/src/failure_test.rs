use super::*;
use crate::any_value::{AnyValueRef, ValueKind, map_addr_from_tagged};
use crate::exec_ctx::ExecCtx;
use crate::heap::SchemaRegistry;
use std::cell::RefCell;
use std::rc::Rc;

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
        raise(process, name, "no cond clause evaluated to a truthy value");
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
