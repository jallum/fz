//! A process raising: the one route every failure takes.
//!
//! `fz_panic` is the runtime primitive behind `Kernel.panic/1`, and so behind
//! `raise`. It reports the raise, then delivers it to the innermost handler on
//! the process's handler stack: a compiled handler is a continuation template
//! that becomes the process's delivered handler closure applied to the raise,
//! the way a receive outcome is materialized; an interpreter handler reads the raise back from
//! `Process::raised`. With no handler the value is rendered as the line Elixir
//! prints for an uncaught exception, that line goes to the execution context's
//! fault sink, and the process is marked failed. The physical export returns
//! either way; the caller unwinds to its quantum entry, which resumes the
//! delivered handler in the same quantum or hands the failed process back to
//! the scheduler.
//!
//! An exception is a map in Elixir's struct shape,
//! `%{__struct__: Name, __exception__: true, message: "..."}`, and prints as
//! `** (Name) message`. Any other value prints the way Elixir prints a raw
//! Erlang error: `** (ErlangError) Erlang error: <value>`.
//!
//! `raise_exception` builds that exception from a name and a message and panics with it.
//! Compiled code reaches it through `fz_raise` and `fz_raise_showing` when a
//! decision raises the exception Elixir raises for it.

use crate::any_value::debug::render_value;
use crate::any_value::{AnyValue, AnyValueRef, ValueKind, map_addr_from_tagged, map_count, map_entry};
use crate::exec_ctx::ExecCtx;
use crate::ir_runtime::bitstring_like_word;
use crate::park::materialize_outcome_closure;
use crate::procbin::{bitstring_bit_len, bitstring_byte_ptr};
use crate::process::{Handler, Process, Raised};
use crate::scheduler_hooks::FaultHook;
use std::io::Write as _;
use std::slice;

/// The line an uncaught failure of `value` prints, as Elixir prints it.
pub fn failure_line(process: *mut Process, value: AnyValue) -> String {
    match exception_name(process, value).zip(exception_message(process, value)) {
        Some((name, message)) => format!("** ({}) {}", render_value(process, name), message),
        None => format!("** (ErlangError) Erlang error: {}", render_value(process, value)),
    }
}

/// The exception's name atom, when `value` is an exception: a map flagged
/// `__exception__: true` whose `__struct__` is an atom. This is the one
/// judgement of what counts as an exception; `rescue` dispatches on its answer.
pub fn exception_name(process: *mut Process, value: AnyValue) -> Option<AnyValue> {
    let is_exception =
        exception_field(process, value, "__exception__").is_some_and(|flag| atom_named(process, flag, "true"));
    let name = exception_field(process, value, "__struct__").filter(|name| name.kind() == ValueKind::ATOM)?;
    is_exception.then_some(name)
}

/// The text of the exception's `message` field, when it is a binary.
fn exception_message(process: *mut Process, value: AnyValue) -> Option<String> {
    binary_text(exception_field(process, value, "message")?)
}

/// One field of a map by atom key; `None` when `value` is not a map or lacks it.
fn exception_field(process: *mut Process, value: AnyValue, name: &str) -> Option<AnyValue> {
    let map = map_addr_from_tagged(value.heap_object_word()?)?;
    (0..unsafe { map_count(map) })
        .map(|index| unsafe { map_entry(map, index) })
        .find(|(key, _)| atom_named(process, *key, name))
        .map(|(_, field)| field)
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

/// The atom every raise from `raise`/`panic` carries as its kind. `throw` and
/// `exit` will add their own kinds to this one stack.
const ERROR_KIND: &str = "error";

/// Raise `value` in the current process. The raise is reported to the
/// context's raise observer, then reaches the innermost handler: a compiled
/// handler becomes the delivered closure applied to `(kind, value, name)`, an
/// interpreter handler receives the same three values through
/// `Process::raised`. With no handler the process fails: its failure line goes
/// to the context's fault sink and `failed` is set. The physical export
/// returns, so each caller unwinds itself: compiled code returns to its
/// quantum entry, the interpreter takes its raised or failed transition.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_panic(process: *mut Process, value_ref: u64) {
    assert!(!process.is_null(), "fz_panic: no current process");
    let process_ptr = process;
    let process = unsafe { &mut *process };
    assert!(!process.ctx.is_null(), "fz_panic: process has no execution context");
    let ctx = unsafe { &*process.ctx };
    let value_ref = AnyValueRef::from_raw_word(value_ref).expect("fz_panic: a value ref");
    let value = AnyValue::from_ref(value_ref).expect("fz_panic: a value");
    let name = exception_name(process_ptr, value);
    report_raise(ctx, process, name, process.handlers.len());
    let Some(handler) = process.handlers.pop() else {
        let line = failure_line(process_ptr, value);
        process.failed = true;
        let sink = ctx.fault.expect("fz_panic: fault sink installed");
        unsafe { sink(ctx.scheduler, line.as_ptr(), line.len()) };
        return;
    };
    let kind = process
        .heap
        .box_any_value_ref(AnyValue::atom(process.node.intern_atom(ERROR_KIND)));
    let name = process.heap.box_any_value_ref(name.unwrap_or(AnyValue::nil_atom()));
    match handler {
        Handler::Closure(template) => {
            let template = template.as_ref().closure_addr().expect("a handler is a closure ref");
            // SAFETY: a handler on the stack is a live closure the collector keeps current.
            let handler = unsafe { materialize_outcome_closure(&mut process.heap, template, &[kind, value_ref, name]) };
            process.deliver_handler(
                AnyValueRef::from_heap_object(ValueKind::CLOSURE, handler).expect("handler closure ref"),
            );
        }
        Handler::Interpreter => {
            process.raised = Some(Raised {
                kind,
                value: value_ref,
                name,
            });
        }
    }
    process.raises_delivered += 1;
}

/// Tell the context's raise observer about a raise: its kind, the exception's
/// name (empty for a value that is not an exception), and how many handlers
/// could receive it.
fn report_raise(ctx: &ExecCtx, process: &Process, name: Option<AnyValue>, depth: usize) {
    let Some(observe) = ctx.raise else {
        return;
    };
    let name = name
        .and_then(|name| match name {
            AnyValue::Atom(id) => process.node.atom_name(id),
            _ => None,
        })
        .unwrap_or_default();
    unsafe {
        observe(
            ctx.scheduler,
            ERROR_KIND.as_ptr(),
            ERROR_KIND.len(),
            name.as_ptr(),
            name.len(),
            depth,
        )
    };
}

/// Fail the current process with the exception `name` carrying `message`,
/// through `fz_panic`.
pub fn raise_exception(process: *mut Process, name: AnyValue, message: &str) {
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
    raise_exception(process, name, &message);
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
    raise_exception(process, name, &message);
}

#[cfg(test)]
#[path = "failure_test.rs"]
mod failure_test;
