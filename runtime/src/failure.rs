//! A process raising: the one route every failure takes.
//!
//! `fz_panic`, `fz_throw` and `fz_exit` are the one route with a fixed kind,
//! behind `Kernel.panic/1`, `throw/1` and `exit/1`; `fz_panic_reason` is
//! `fz_panic` for a failure that has an Erlang reason beside its exception, the
//! one a `Term::Raise` with a reason compiles to, and
//! `fz_reraise` continues a raise a handler was delivered, with the kind and
//! reason it arrived with. A raise reports itself, then goes to
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
//! An exception is a struct whose `__exception__` field is `true`. Its words
//! belong to
//! its module, so the line for an uncaught error is rendered by the handler
//! the compiler places at the bottom of every process, which ends the process
//! through `fz_fail` with that line. An error that reaches this module with
//! no handler left was raised by that bottom handler itself, or in a process
//! that has none, such as a macro the compiler is expanding. No module can be
//! asked there, so an exception that carries its words in a binary `message`
//! field prints as `** (Name) message`, and any other value the way Elixir
//! prints a raw Erlang error: `** (ErlangError) Erlang error: <value>`. A
//! throw prints
//! `** (throw) <value>` and an exit `** (exit) <reason>`, except an exit whose
//! reason is a shutdown, which prints nothing.
//!
//! `raise_exception` builds a struct of an exception's module from its fields
//! and raises it as an error, for a failure whose exception is chosen as the
//! process runs. Compiled code builds the struct itself when a decision raises
//! the exception Elixir raises for it, and raises it through `fz_panic`.

use crate::any_value::debug::render_value;
use crate::any_value::{AnyValue, AnyValueRef, Stored, ValueKind};
use crate::bits::{Bin, is_bitstring_like};
use crate::exec_ctx::ExecCtx;
use crate::handler_stack::Innermost;
use crate::heap::{list_head_ref, list_tail_ref};
use crate::ir_runtime::{fz_tuple_elem, fz_tuple_size};
use crate::module_name::ModuleName;
use crate::park::materialize_outcome_closure;
use crate::process::{Process, Raised};
use crate::scheduler_hooks::FaultHook;
use std::io::Write as _;
use std::slice;

/// The field whose `true` marks a struct as an exception.
pub const EXCEPTION_FIELD: &str = "__exception__";

/// The three kinds of raise. They share one route: a handler receives the kind
/// as the atom named by `name`, beside the raised value and its reason.
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

    pub const ALL: [Self; 3] = [Self::Error, Self::Throw, Self::Exit];

    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|kind| kind.name() == name)
    }
}

/// The status an uncaught exit leaves its process with when the reason is a
/// shutdown, as Elixir's CLI reads it: `:normal` and `:shutdown` are 0,
/// `{:shutdown, status}` is `status` and any other `{:shutdown, _}` is 0.
/// Every other reason is not a shutdown.
fn shutdown_status(process: *mut Process, reason: AnyValue) -> Option<i32> {
    if atom_named(process, reason, "normal") || atom_named(process, reason, "shutdown") {
        return Some(0);
    }
    let AnyValue::HeapRef(tuple) = reason else {
        return None;
    };
    let word = tuple.raw_word();
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
pub fn exit_status(process: *mut Process, kind: RaiseKind, value: AnyValue) -> i32 {
    match kind {
        RaiseKind::Exit => shutdown_status(process, value).unwrap_or(1),
        RaiseKind::Error | RaiseKind::Throw => 1,
    }
}

/// The line an uncaught raise of `kind` and `value` prints, as Elixir prints
/// it; `None` for an exit whose reason is a shutdown, which ends silently.
pub fn failure_line(process: *mut Process, kind: RaiseKind, value: AnyValue) -> Option<String> {
    let rendered = value;
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

/// The exception's name atom, when `value` is an exception: a map, in either
/// layout, flagged `__exception__: true` whose `__struct__` is an atom. This is the one
/// judgement of what counts as an exception; `rescue` dispatches on its answer.
pub fn exception_name(process: *mut Process, value: AnyValue) -> Option<AnyValue> {
    let is_exception =
        exception_field(process, value, EXCEPTION_FIELD).is_some_and(|flag| atom_named(process, flag, "true"));
    let name = exception_field(process, value, "__struct__").filter(|name| name.kind() == ValueKind::ATOM)?;
    is_exception.then_some(name)
}

/// The text of the exception's `message` field, when it is a binary.
fn exception_message(process: *mut Process, value: AnyValue) -> Option<String> {
    binary_text(exception_field(process, value, "message")?)
}

/// One field of a map, in either layout, by atom key; `None` when `value` is
/// not a map or lacks it.
fn exception_field(process: *mut Process, value: AnyValue, name: &str) -> Option<AnyValue> {
    let AnyValue::HeapRef(value) = value else {
        return None;
    };
    let process = unsafe { process.as_mut()? };
    let key = AnyValue::atom(process.node.intern_atom(name));
    let layout = process.heap.map_layout(value)?;
    let field = process.heap.map_view_get(layout, key)?;
    AnyValue::from_ref(field).ok()
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
    if !is_bitstring_like(value.raw_word()) {
        return None;
    }
    let binary = unsafe { Bin::of_binary(value.raw_word()) };
    if !binary.bit_len().is_multiple_of(8) {
        return None;
    }
    let bytes = binary.bytes();
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
pub extern "C" fn fz_panic(process: *mut Process, value_word: u64, value_kind: u64) {
    raise(
        process,
        RaiseKind::Error,
        Stored {
            word: value_word,
            kind: value_kind,
        },
        None,
    );
}

/// Raise `value` in the current process as an error that has an Erlang
/// reason: the primitive a `Term::Raise` with a reason compiles to, and the one
/// the interpreter raises a `LastResort::Raise` through. A `catch :error, reason`
/// clause binds the reason; a `rescue` binds `value`.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_panic_reason(
    process: *mut Process,
    value_word: u64,
    value_kind: u64,
    reason_word: u64,
    reason_kind: u64,
) {
    raise(
        process,
        RaiseKind::Error,
        Stored {
            word: value_word,
            kind: value_kind,
        },
        Some(Stored {
            word: reason_word,
            kind: reason_kind,
        }),
    );
}

/// Raise `value` in the current process as a throw: the primitive behind
/// `Kernel.throw/1`.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_throw(process: *mut Process, value_word: u64, value_kind: u64) {
    raise(
        process,
        RaiseKind::Throw,
        Stored {
            word: value_word,
            kind: value_kind,
        },
        None,
    );
}

/// Raise `reason` in the current process as an exit: the primitive behind
/// `Kernel.exit/1`.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_exit(process: *mut Process, reason_word: u64, reason_kind: u64) {
    raise(
        process,
        RaiseKind::Exit,
        Stored {
            word: reason_word,
            kind: reason_kind,
        },
        None,
    );
}

/// End the current process as an uncaught error ends it, with `line` as the
/// line it prints: the primitive behind `Exception.__uncaught__/1`, which
/// renders the line from the exception's own module.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_fail(process: *mut Process, line_ref: u64) {
    assert!(!process.is_null(), "fz_fail: no current process");
    let line = binary_text(value_from_word(line_ref, "fz_fail line")).expect("fz_fail: a binary line");
    let process = unsafe { &mut *process };
    assert!(!process.ctx.is_null(), "fz_fail: process has no execution context");
    let ctx = unsafe { &*process.ctx };
    process.fail(1);
    let sink = ctx.fault.expect("fz_fail: fault sink installed");
    unsafe { sink(ctx.scheduler, line.as_ptr(), line.len()) };
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
    process.fail(status);
}

/// Continue the raise a handler was delivered: raise `value` with the kind
/// the handler received, as the atom `kind`, and the reason it received. The
/// compiler re-raises only what a handler was delivered, so a kind the runtime
/// never delivers is a fault in the compiler, not a program's error.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub fn reraise(process: *mut Process, kind: AnyValue, value: Stored, reason: Stored) {
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
    raise(process, kind, value, Some(reason));
}

/// [`reraise`] for compiled code: `kind_ref` is the atom the handler received.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_reraise(
    process: *mut Process,
    kind_ref: u64,
    value_word: u64,
    value_kind: u64,
    reason_word: u64,
    reason_kind: u64,
) {
    reraise(
        process,
        value_from_word(kind_ref, "fz_reraise kind"),
        Stored {
            word: value_word,
            kind: value_kind,
        },
        Stored {
            word: reason_word,
            kind: reason_kind,
        },
    );
}

/// Report the raise to the context's raise observer, then deliver it to the
/// innermost handler: a compiled handler becomes the delivered closure applied
/// to `(kind, value, reason, name)`, an interpreter handler receives the same
/// four values through `Process::raised`. The reason is the one the raise
/// carries, or the raised value when it carries none. With no handler the process ends: its
/// status is recorded, its failure line, when it has one, goes to the context's
/// fault sink, and `failed` is set. The physical export returns, so each caller
/// unwinds itself: compiled code returns to its quantum entry, the interpreter
/// takes its raised or failed transition.
fn raise(process: *mut Process, kind: RaiseKind, raised: Stored, reason: Option<Stored>) {
    assert!(!process.is_null(), "raise: no current process");
    let process_ptr = process;
    let process = unsafe { &mut *process };
    assert!(!process.ctx.is_null(), "raise: process has no execution context");
    let ctx = unsafe { &*process.ctx };
    let value = raised.value("raise");
    let reason = reason.unwrap_or(raised);
    let name = exception_name(process_ptr, value);
    let stack_marker = 0u8;
    let stack_bytes = match process.stack_base {
        0 => 0,
        base => base.saturating_sub(&stack_marker as *const u8 as usize),
    };
    report_raise(ctx, process, kind, name, process.handlers.depth(), stack_bytes);
    let Some(handler) = process.handlers.innermost() else {
        let line = failure_line(process_ptr, kind, value);
        let status = exit_status(process_ptr, kind, value);
        process.fail(status);
        if let Some(line) = line {
            let sink = ctx.fault.expect("raise: fault sink installed");
            unsafe { sink(ctx.scheduler, line.as_ptr(), line.len()) };
        }
        return;
    };
    let kind = Stored::of(AnyValue::atom(process.node.intern_atom(kind.name())));
    let name = Stored::of(name.unwrap_or(AnyValue::nil_atom()));
    match handler {
        Innermost::Compiled(image) => {
            // SAFETY: a compiled record is a closure image the collector keeps current.
            let handler =
                unsafe { materialize_outcome_closure(&mut process.heap, image, &[kind, raised, reason, name]) };
            process.pop_handler();
            process.deliver_handler(
                AnyValueRef::from_heap_object(ValueKind::CLOSURE, handler).expect("handler closure ref"),
            );
        }
        Innermost::Interpreter => {
            process.pop_handler();
            process.raised = Some(Raised {
                kind,
                value: raised,
                name,
                reason,
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
    let name = name.and_then(|name| match name {
        AnyValue::Atom(id) => process.node.atom_name(id),
        _ => None,
    });
    let name = name.as_deref().unwrap_or_default();
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

/// Raise the exception `name` with `fields` in the current process, as an
/// error, through the one route. `reason` is the Erlang reason the failure
/// declares, when it declares one.
pub fn raise_exception(process: *mut Process, name: AnyValue, fields: &[(&str, AnyValue)], reason: Option<AnyValue>) {
    let exception = exception(process, name, fields);
    raise(process, RaiseKind::Error, Stored::of(exception), reason.map(Stored::of));
}

/// Raise what Elixir raises when `receiver.function(..)` with `arity`
/// arguments finds nothing to call. A receiver that is no atom is an
/// `ArgumentError`. An atom is an `UndefinedFunctionError` carrying the module,
/// the function and the arity; `module_is_defined` says whether the atom names
/// a module that lacks the function or names no module at all.
pub fn raise_undefined_function(
    process: *mut Process,
    receiver: AnyValue,
    function: AnyValue,
    arity: i64,
    module_is_defined: bool,
) {
    let shown = render_value(process, receiver);
    if !matches!(receiver, AnyValue::Atom(_)) {
        let message = not_a_module_message(&shown, &render_value(process, function), arity);
        let message = text(process, &message);
        return raise_exception(
            process,
            atom(process, "Elixir.ArgumentError"),
            &[("message", message)],
            None,
        );
    }
    let called = format!("{shown}.{}/{arity}", atom_text(process, function));
    let message = if module_is_defined {
        format!("function {called} is undefined or private")
    } else if atom_named(process, receiver, "nil") {
        format!("function {called} is undefined")
    } else {
        format!("function {called} is undefined (module {shown} is not available)")
    };
    let message = text(process, &message);
    raise_exception(
        process,
        atom(process, "Elixir.UndefinedFunctionError"),
        &[
            ("module", receiver),
            ("function", function),
            ("arity", AnyValue::Int(arity)),
            ("reason", atom(process, "nil")),
            ("message", message),
        ],
        Some(atom(process, "undef")),
    );
}

fn not_a_module_message(receiver: &str, function: &str, arity: i64) -> String {
    if arity == 0 {
        format!(
            "you attempted to apply a function named {function} on {receiver}. If you are using Kernel.apply/3, \
             make sure the module is an atom. If you are using the dot syntax, such as module.function(), make \
             sure the left-hand side of the dot is an atom representing a module"
        )
    } else {
        format!(
            "you attempted to apply a function on {receiver}. Modules (the first argument of apply) must always \
             be an atom"
        )
    }
}

fn atom(process: *mut Process, name: &str) -> AnyValue {
    AnyValue::atom(unsafe { &*process }.node.intern_atom(name))
}

fn atom_text(process: *mut Process, value: AnyValue) -> String {
    let AnyValue::Atom(id) = value else {
        panic!("a function name is an atom, not {value:?}")
    };
    unsafe { &*process }
        .node
        .atom_name(id)
        .unwrap_or_else(|| panic!("atom {id} has no name"))
        .to_string()
}

fn text(process: *mut Process, text: &str) -> AnyValue {
    let process = unsafe { &mut *process };
    process.alloc_bitstring(text.as_bytes(), 8 * text.len() as u64)
}

/// A struct of the exception module `name` on the process heap: `fields` gives every field the module declares but the
/// `__exception__` mark, which is `true`. The module's struct is registered
/// with the heap before anything raises it.
fn exception(process: *mut Process, name: AnyValue, fields: &[(&str, AnyValue)]) -> AnyValue {
    let marked = atom(process, "true");
    let process = unsafe { &mut *process };
    let module = match name {
        AnyValue::Atom(id) => process.node.atom_name(id),
        _ => None,
    };
    let module = module
        .and_then(|name| ModuleName::from_atom_name(name.as_str()))
        .unwrap_or_else(|| panic!("an exception is named by its module's atom, not {name:?}"));
    let registry = process.heap.schemas_registry();
    let schema_id = registry
        .borrow()
        .named(&module)
        .unwrap_or_else(|| panic!("exception `{module}` is raised before its struct is registered"));
    let declared: Vec<Option<String>> = registry
        .borrow()
        .get(schema_id)
        .fields
        .iter()
        .map(|field| field.name.clone())
        .collect();
    assert_eq!(
        declared.len(),
        fields.len() + 1,
        "exception `{module}` is given each field it declares but `{EXCEPTION_FIELD}`"
    );
    let object = process.heap.alloc_struct(schema_id);
    for (index, field) in declared.iter().enumerate() {
        let field = field.as_deref().expect("a struct's field has a name");
        let value = if field == EXCEPTION_FIELD {
            marked
        } else {
            let given = fields.iter().find(|(name, _)| *name == field);
            given
                .unwrap_or_else(|| panic!("exception `{module}` is raised with no `{field}`"))
                .1
        };
        unsafe { process.heap.write_field_slot(object, (index * 8) as u32, value) };
    }
    AnyValue::HeapRef(AnyValueRef::from_heap_object(ValueKind::STRUCT, object).expect("an exception struct ref"))
}

fn value_from_word(word: u64, context: &str) -> AnyValue {
    AnyValueRef::from_raw_word(word)
        .and_then(AnyValue::from_ref)
        .unwrap_or_else(|error| panic!("{context}: a value ref ({error:?})"))
}

/// Raise for a call `receiver.function(..)` that reached no function.
/// `modules_ref` lists the atoms naming a module that lacks the function.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_raise_undefined_function(
    process: *mut Process,
    receiver_ref: u64,
    function_ref: u64,
    arity: i64,
    modules_ref: u64,
) {
    let receiver = value_from_word(receiver_ref, "fz_raise_undefined_function receiver");
    let function = value_from_word(function_ref, "fz_raise_undefined_function function");
    let mut modules = AnyValueRef::from_raw_word(modules_ref).expect("fz_raise_undefined_function: a list ref");
    let mut module_is_defined = false;
    while !module_is_defined && !modules.is_empty_list() {
        let head = list_head_ref(modules).and_then(AnyValue::from_ref);
        module_is_defined = head.expect("fz_raise_undefined_function: a list of atoms") == receiver;
        modules = list_tail_ref(modules).expect("fz_raise_undefined_function: a list tail");
    }
    raise_undefined_function(process, receiver, function, arity, module_is_defined);
}

#[cfg(test)]
#[path = "failure_test.rs"]
mod failure_test;
