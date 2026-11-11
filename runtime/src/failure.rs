//! A process failing: the one route every uncaught failure takes.
//!
//! `fz_panic` is the runtime primitive behind `Kernel.panic/1`. It renders the
//! value it was given as the line Elixir prints for an uncaught exception,
//! hands that line to the execution context's fault sink, and marks the
//! process failed. The caller then ends the process through the normal exit
//! path; nothing after a panic runs.
//!
//! An exception is a map in Elixir's struct shape,
//! `%{__struct__: Name, __exception__: true, message: "..."}`, and prints as
//! `** (Name) message`. Any other value prints the way Elixir prints a raw
//! Erlang error: `** (ErlangError) Erlang error: <value>`.
//!
//! `raise` builds that exception from a name and a message and panics with it.
//! Compiled code reaches it through `fz_raise` and `fz_raise_showing` when a
//! decision raises the exception Elixir raises for it.

use crate::any_value::debug::render_value;
use crate::any_value::{AnyValue, AnyValueRef, ValueKind, map_addr_from_tagged, map_count, map_entry};
use crate::ir_runtime::bitstring_like_word;
use crate::procbin::{bitstring_bit_len, bitstring_byte_ptr};
use crate::process::Process;
use crate::scheduler_hooks::FaultHook;
use std::io::Write as _;
use std::slice;

/// The line an uncaught failure of `value` prints, as Elixir prints it.
pub fn failure_line(process: *mut Process, value: AnyValue) -> String {
    match exception_parts(process, value) {
        Some((name, message)) => format!("** ({}) {}", render_value(process, name), message),
        None => format!("** (ErlangError) Erlang error: {}", render_value(process, value)),
    }
}

/// The exception's name and message, when `value` is an exception.
fn exception_parts(process: *mut Process, value: AnyValue) -> Option<(AnyValue, String)> {
    let map = map_addr_from_tagged(value.heap_object_word()?)?;
    let field = |name: &str| {
        (0..unsafe { map_count(map) })
            .map(|index| unsafe { map_entry(map, index) })
            .find(|(key, _)| atom_named(process, *key, name))
            .map(|(_, field)| field)
    };
    let is_exception = field("__exception__").is_some_and(|flag| atom_named(process, flag, "true"));
    let name = field("__struct__").filter(|name| name.kind() == ValueKind::ATOM)?;
    let message = binary_text(field("message")?)?;
    is_exception.then_some((name, message))
}

fn atom_named(process: *mut Process, value: AnyValue, name: &str) -> bool {
    let AnyValue::Atom(id) = value else {
        return false;
    };
    !process.is_null() && unsafe { &*process }.node.atom_name(id).as_deref() == Some(name)
}

/// The text of a byte-aligned binary.
fn binary_text(value: AnyValue) -> Option<String> {
    let AnyValue::HeapRef(value) = value else {
        return None;
    };
    let p = bitstring_like_word(value.raw_word())?;
    let bit_len = unsafe { bitstring_bit_len(p) } as usize;
    if !bit_len.is_multiple_of(8) {
        return None;
    }
    let bytes = unsafe { slice::from_raw_parts(bitstring_byte_ptr(p), bit_len / 8) };
    Some(String::from_utf8_lossy(bytes).into_owned())
}

/// The fault sink of a process whose failures are the program's own: its line
/// goes to stderr.
pub const STDERR_FAULT_HOOK: FaultHook = stderr_fault_hook;

unsafe extern "C" fn stderr_fault_hook(_context: *mut (), line: *const u8, len: usize) {
    let mut stderr = std::io::stderr().lock();
    let _ = stderr.write_all(unsafe { slice::from_raw_parts(line, len) });
    let _ = stderr.write_all(b"\n");
}

/// Fail the current process with `value`: its failure line goes to the
/// context's fault sink and the process is marked failed. The physical export
/// returns, so each caller ends the process itself: compiled code returns to
/// the scheduler, the interpreter takes its failed transition.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_panic(process: *mut Process, value_ref: u64) {
    assert!(!process.is_null(), "fz_panic: no current process");
    let ctx = unsafe { (*process).ctx };
    assert!(!ctx.is_null(), "fz_panic: process has no execution context");
    let ctx = unsafe { &*ctx };
    let value = AnyValueRef::from_raw_word(value_ref)
        .and_then(AnyValue::from_ref)
        .expect("fz_panic: a value ref");
    let line = failure_line(process, value);
    unsafe { &mut *process }.failed = true;
    let sink = ctx.fault.expect("fz_panic: fault sink installed");
    unsafe { sink(ctx.scheduler, line.as_ptr(), line.len()) };
}

/// Fail the current process with the exception `name` carrying `message`,
/// through `fz_panic`.
pub fn raise(process: *mut Process, name: AnyValue, message: &str) {
    let exception = exception(process, name, message);
    fz_panic(process, exception);
}

/// The message of an exception about a term, the way Elixir words one: the
/// lead, then the term on a line of its own, indented.
pub fn message_showing(process: *mut Process, lead: &str, term: AnyValue) -> String {
    format!("{lead}\n\n    {}\n", render_value(process, term))
}

/// `%{__struct__: name, __exception__: true, message: message}` on the
/// process heap, as a value word.
fn exception(process: *mut Process, name: AnyValue, message: &str) -> u64 {
    let process = unsafe { &mut *process };
    let atom = |name: &str| AnyValue::atom(process.node.intern_atom(name));
    let (struct_key, exception_key, message_key, flag) =
        (atom("__struct__"), atom("__exception__"), atom("message"), atom("true"));
    let message = process
        .heap
        .alloc_bitstring(message.as_bytes(), 8 * message.len() as u64);
    let bits = process
        .heap
        .alloc_map_slots(&[(struct_key, name), (exception_key, flag), (message_key, message)]);
    let addr = map_addr_from_tagged(bits).expect("an exception is a map");
    AnyValueRef::from_heap_object(ValueKind::MAP, addr)
        .expect("an exception map ref")
        .raw_word()
}

fn value_from_word(word: u64, context: &str) -> AnyValue {
    AnyValueRef::from_raw_word(word)
        .and_then(AnyValue::from_ref)
        .unwrap_or_else(|error| panic!("{context}: a value ref ({error:?})"))
}

/// Raise the exception named by the atom `name_ref` with the binary
/// `message_ref` as its message.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_raise(process: *mut Process, name_ref: u64, message_ref: u64) {
    let name = value_from_word(name_ref, "fz_raise name");
    let message = binary_text(value_from_word(message_ref, "fz_raise message")).expect("fz_raise: a binary message");
    raise(process, name, &message);
}

/// Raise the exception named by the atom `name_ref` with a message about the
/// term `term_ref`, led by the binary `lead_ref`.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_raise_showing(process: *mut Process, name_ref: u64, lead_ref: u64, term_ref: u64) {
    let name = value_from_word(name_ref, "fz_raise_showing name");
    let lead =
        binary_text(value_from_word(lead_ref, "fz_raise_showing lead")).expect("fz_raise_showing: a binary lead");
    let term = value_from_word(term_ref, "fz_raise_showing term");
    let message = message_showing(process, &lead, term);
    raise(process, name, &message);
}

#[cfg(test)]
#[path = "failure_test.rs"]
mod failure_test;
