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

use crate::any_value::debug::render_value;
use crate::any_value::{AnyValue, AnyValueRef, ValueKind, map_addr_from_tagged, map_count, map_entry};
use crate::ir_runtime::bitstring_like_ptr_from_ref;
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
    let p = bitstring_like_ptr_from_ref(value.raw_word())?;
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

#[cfg(test)]
#[path = "failure_test.rs"]
mod failure_test;
