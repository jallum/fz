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
        let reason = atom(process, "function_clause");
        assert_eq!(
            failure_line(process, reason),
            "** (ErlangError) Erlang error: :function_clause"
        );
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
