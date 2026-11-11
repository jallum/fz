//! A process raising: the one route every failure takes.
//!
//! `fz_panic`, `fz_throw` and `fz_exit` are the one route with a fixed kind,
//! behind `Kernel.panic/1`, `throw/1` and `exit/1`; `fz_reraise` continues a
//! raise a handler was delivered, with the kind it arrived with. A raise
//! reports itself, then goes to
//! the innermost handler on the process's handler stack: a compiled handler is
//! a continuation template that becomes the process's delivered handler closure
//! applied to the raise, the way a receive outcome is materialized; an
//! interpreter handler reads the raise back from `Process::raised`. With no
//! handler the raise is rendered as the line Elixir prints for it, that line
//! goes to the execution context's fault sink, and the process is marked
//! failed with the exit status its kind and value give. The physical export
//! returns either way; the caller unwinds to its quantum entry, which resumes
//! the delivered handler in the same quantum or hands the failed process back
//! to the scheduler.
//!
//! An exception is a map in Elixir's struct shape,
//! `%{__struct__: Name, __exception__: true, message: "..."}`, and prints as
//! `** (Name) message`. Any other error value prints the way Elixir prints a
//! raw Erlang error: `** (ErlangError) Erlang error: <value>`. A throw prints
//! `** (throw) <value>` and an exit `** (exit) <reason>`, except an exit whose
//! reason is a shutdown, which prints nothing.
//!
//! `raise_exception` builds an exception from a name and a message and raises
//! it as an error; `raise_exception_showing` also carries the term the message
//! shows, in the exception's `term` field. Compiled code reaches it through `fz_raise` and
//! `fz_raise_showing` when a decision raises the exception Elixir raises for
//! it, and `Kernel.raise/2` calls `fz_raise`.

use crate::any_value::debug::render_value;
use crate::any_value::{AnyValue, AnyValueRef, ValueKind, map_addr_from_tagged, map_count, map_entry};
use crate::exec_ctx::ExecCtx;
use crate::ir_runtime::{bitstring_like_word, fz_tuple_elem, fz_tuple_size};
use crate::park::materialize_outcome_closure;
use crate::procbin::{bitstring_bit_len, bitstring_byte_ptr};
use crate::process::{Handler, Process, Raised};
use crate::scheduler_hooks::FaultHook;
use std::io::Write as _;
use std::slice;

/// The three kinds of raise. They share one route: a handler receives the kind
/// as the atom named by `name`, beside the raised value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RaiseKind {
    /// `raise`, `panic` and the runtime's own traps.
    Error,
    /// `throw`.
    Throw,
    /// `exit`.
    Exit,
}

impl RaiseKind {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Error => "error",
            Self::Throw => "throw",
            Self::Exit => "exit",
        }
    }

    fn from_name(name: &str) -> Option<Self> {
        [Self::Error, Self::Throw, Self::Exit]
            .into_iter()
            .find(|kind| kind.name() == name)
    }
}

/// The status an uncaught exit leaves its process with when the reason is a
/// shutdown, as Elixir's CLI reads it: `:normal` and `:shutdown` are 0,
/// `{:shutdown, status}` is `status` and any other `{:shutdown, _}` is 0.
/// Every other reason is not a shutdown.
fn shutdown_status(process: *mut Process, reason: AnyValueRef) -> Option<i32> {
    let word = reason.raw_word();
    let value = AnyValue::from_ref(reason).ok()?;
    if atom_named(process, value, "normal") || atom_named(process, value, "shutdown") {
        return Some(0);
    }
    if fz_tuple_size(process, word) != 2 {
        return None;
    }
    let field = |index| value_of_word(fz_tuple_elem(process, word, index));
    if !atom_named(process, field(0)?, "shutdown") {
        return None;
    }
    Some(match field(1)? {
        AnyValue::Int(status) => status as i32,
        _ => 0,
    })
}

fn value_of_word(word: u64) -> Option<AnyValue> {
    AnyValue::from_ref(AnyValueRef::from_raw_word(word).ok()?).ok()
}

/// The status a process ends with when a raise of `kind` and `value` reaches no
/// handler: 1, except for an exit whose reason is a shutdown.
pub fn exit_status(process: *mut Process, kind: RaiseKind, value: AnyValueRef) -> i32 {
    match kind {
        RaiseKind::Exit => shutdown_status(process, value).unwrap_or(1),
        RaiseKind::Error | RaiseKind::Throw => 1,
    }
}

/// The line an uncaught raise of `kind` and `value` prints, as Elixir prints
/// it; `None` for an exit whose reason is a shutdown, which ends silently.
pub fn failure_line(process: *mut Process, kind: RaiseKind, value: AnyValueRef) -> Option<String> {
    let rendered = AnyValue::from_ref(value).expect("failure_line: a value");
    match kind {
        RaiseKind::Error => Some(
            match exception_name(process, rendered).zip(exception_message(process, rendered)) {
                Some((name, message)) => format!("** ({}) {}", render_value(process, name), message),
                None => format!("** (ErlangError) Erlang error: {}", render_value(process, rendered)),
            },
        ),
        RaiseKind::Throw => Some(format!("** (throw) {}", render_value(process, rendered))),
        RaiseKind::Exit => shutdown_status(process, value)
            .is_none()
            .then(|| format!("** (exit) {}", render_value(process, rendered))),
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

/// Raise `value` in the current process as an error: the primitive behind
/// `Kernel.panic/1`, and the one the runtime's own traps use.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_panic(process: *mut Process, value_ref: u64) {
    raise(process, RaiseKind::Error, value_ref);
}

/// Raise `value` in the current process as a throw: the primitive behind
/// `Kernel.throw/1`.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_throw(process: *mut Process, value_ref: u64) {
    raise(process, RaiseKind::Throw, value_ref);
}

/// Raise `reason` in the current process as an exit: the primitive behind
/// `Kernel.exit/1`.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_exit(process: *mut Process, reason_ref: u64) {
    raise(process, RaiseKind::Exit, reason_ref);
}

/// `System.halt/1`: end the program with `status`. The context's scheduler
/// records the end, and the calling process ends the way an uncaught raise ends
/// it, without the failure line and without a handler search: its `try` bodies,
/// `catch` clauses and `after` blocks never run, and the frames above unwind as
/// they do for a failed process.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_system_halt(process: *mut Process, status: i64) {
    assert!(!process.is_null(), "fz_system_halt: no current process");
    let process = unsafe { &mut *process };
    assert!(
        !process.ctx.is_null(),
        "fz_system_halt: process has no execution context"
    );
    let ctx = unsafe { &*process.ctx };
    let status = status as i32;
    let halt = ctx.halt.expect("fz_system_halt: halt hook installed");
    halt(ctx.scheduler, status);
    process.failed = true;
    process.exit_status = status;
}

/// Continue the raise a handler was delivered: raise `value_ref` with the kind
/// the handler received, as the atom `kind`. The compiler re-raises only what a
/// handler was delivered, so a kind the runtime never delivers is a fault in
/// the compiler, not a program's error.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub fn reraise(process: *mut Process, kind: AnyValue, value_ref: u64) {
    assert!(!process.is_null(), "reraise: no current process");
    let node = unsafe { &*process }.node.clone();
    let name = match kind {
        AnyValue::Atom(id) => node.atom_name(id),
        _ => None,
    };
    let kind = name
        .as_deref()
        .and_then(RaiseKind::from_name)
        .unwrap_or_else(|| panic!("fz_reraise: the kind {name:?} is not one the runtime delivers"));
    raise(process, kind, value_ref);
}

/// [`reraise`] for compiled code: `kind_ref` is the atom the handler received.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_reraise(process: *mut Process, kind_ref: u64, value_ref: u64) {
    reraise(process, value_from_word(kind_ref, "fz_reraise kind"), value_ref);
}

/// Report the raise to the context's raise observer, then deliver it to the
/// innermost handler: a compiled handler becomes the delivered closure applied
/// to `(kind, value, name)`, an interpreter handler receives the same three
/// values through `Process::raised`. With no handler the process ends: its
/// status is recorded, its failure line, when it has one, goes to the context's
/// fault sink, and `failed` is set. The physical export returns, so each caller
/// unwinds itself: compiled code returns to its quantum entry, the interpreter
/// takes its raised or failed transition.
fn raise(process: *mut Process, kind: RaiseKind, value_ref: u64) {
    assert!(!process.is_null(), "raise: no current process");
    let process_ptr = process;
    let process = unsafe { &mut *process };
    assert!(!process.ctx.is_null(), "raise: process has no execution context");
    let ctx = unsafe { &*process.ctx };
    let value_ref = AnyValueRef::from_raw_word(value_ref).expect("raise: a value ref");
    let value = AnyValue::from_ref(value_ref).expect("raise: a value");
    let name = exception_name(process_ptr, value);
    let stack_marker = 0u8;
    let stack_bytes = match process.stack_base {
        0 => 0,
        base => base.saturating_sub(&stack_marker as *const u8 as usize),
    };
    report_raise(ctx, process, kind, name, process.handlers.len(), stack_bytes);
    let Some(handler) = process.handlers.pop() else {
        let line = failure_line(process_ptr, kind, value_ref);
        process.failed = true;
        process.exit_status = exit_status(process_ptr, kind, value_ref);
        if let Some(line) = line {
            let sink = ctx.fault.expect("raise: fault sink installed");
            unsafe { sink(ctx.scheduler, line.as_ptr(), line.len()) };
        }
        return;
    };
    let kind = process
        .heap
        .box_any_value_ref(AnyValue::atom(process.node.intern_atom(kind.name())));
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
/// could receive it, and how many bytes of machine stack lie between the
/// quantum's entry and the raise.
fn report_raise(
    ctx: &ExecCtx,
    process: &Process,
    kind: RaiseKind,
    name: Option<AnyValue>,
    depth: usize,
    stack_bytes: usize,
) {
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
            kind.name().as_ptr(),
            kind.name().len(),
            name.as_ptr(),
            name.len(),
            depth,
            stack_bytes,
        )
    };
}

/// Raise the exception `name` carrying `message` in the current process, as an
/// error, through the one route.
pub fn raise_exception(process: *mut Process, name: AnyValue, message: &str) {
    let message = text(process, message);
    let exception = exception(process, name, &[("message", message)]);
    raise(process, RaiseKind::Error, exception);
}

/// Raise the exception `name` about `term`, the way Elixir's `CaseClauseError`
/// and its kin do: `message` is `lead`, then the term on a line of its own,
/// indented, and the exception carries the term itself in `term`.
pub fn raise_exception_showing(process: *mut Process, name: AnyValue, lead: &str, term: AnyValue) {
    let message = text(process, &format!("{lead}\n\n    {}\n", render_value(process, term)));
    let exception = exception(process, name, &[("message", message), ("term", term)]);
    raise(process, RaiseKind::Error, exception);
}

fn text(process: *mut Process, text: &str) -> AnyValue {
    let process = unsafe { &mut *process };
    process.heap.alloc_bitstring(text.as_bytes(), 8 * text.len() as u64)
}

/// `%{__struct__: name, __exception__: true, ..fields}` on the process heap, as
/// a value word.
fn exception(process: *mut Process, name: AnyValue, fields: &[(&str, AnyValue)]) -> u64 {
    let process = unsafe { &mut *process };
    let atom = |name: &str| AnyValue::atom(process.node.intern_atom(name));
    let mut entries = vec![(atom("__struct__"), name), (atom("__exception__"), atom("true"))];
    entries.extend(fields.iter().map(|&(key, value)| (atom(key), value)));
    let bits = process.heap.alloc_map_slots(&entries);
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
    raise_exception_showing(process, name, &lead, term);
}

#[cfg(test)]
#[path = "failure_test.rs"]
mod failure_test;
