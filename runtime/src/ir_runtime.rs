//! Runtime helpers for the fz JIT — the `extern "C"` fns the generated
//! Cranelift code calls into. Any execution path (JIT, AOT) can
//! link against this FFI surface without dragging the JIT module along.
//!
//! The file is organised in clusters:
//!   arith / cmp / eq
//!   alloc
//!   map         (fz_map_*, fz_key_*)
//!   bitstring   (fz_bs_*, decode_*/encode_* bit helpers)
//!   closure     (fz_closure_*, fz_tail_closure)
//!   concurrency (fz_spawn, fz_self, fz_send, fz_receive_attempt)
//!   halt/print  (fz_halt, fz_io_write)
//!
//! All fns here have unstable `extern "C"` ABI — they're called by
//! Cranelift-emitted code via the symbol-binding list in
//! `ir_codegen::compile`. Do not reorder args or change return types
//! without updating the matching `declare_function` signatures.
//!
//! Every BIF takes its `*mut Process` (or value-ref ptr) from the caller — the
//! pinned register for compiled code, a threaded param for the interpreter —
//! and dereferences it. That's the entire purpose of this FFI surface, so the
//! `not_unsafe_ptr_arg_deref` lint is allowed module-wide instead of per-fn.
#![allow(clippy::not_unsafe_ptr_arg_deref)]

use crate::any_value::debug::{Limits, render_value, render_with_limits};
use crate::any_value::{
    AnyValue, AnyValueRef, FALSE_ATOM_ID, ListCons, NIL_ATOM_ID, SlotLayout, Stored, ValueKind,
    binview_addr_from_tagged, closure_addr_from_tagged, closure_arity, closure_capture_ref_word,
    closure_captured_count, closure_denotation, closure_fn_ptr, closure_halt_kind, map_addr_from_tagged, object_size,
    struct_is_named, struct_is_shared, struct_schema_id,
};
use crate::bits::{
    Bin, BinView, SharedBin, SharedBinHandle, alloc_buffer_view, is_bitstring_like, referenced_byte_len,
};
use crate::bitstr::{BitReader, BitType, Endian, apply_endian_for_read, sign_extend};
use crate::construction::{self, FzBsField};
use crate::exec_ctx::ExecCtx;
use crate::heap::{AllocStat, MapPart, StubSite, closure_capture_ref, list_head_ref, list_tail_ref};
use crate::module_name::STRUCT_MODULE_FIELD;
use crate::park::{ParkRecord, ReceiveSite};
use crate::process::Process;
use crate::resource::{ResourceHandle, ResourceStub, alloc_resource};
use crate::reuse_site::RuntimeReuseSite;
use crate::sched::{ReceiveStep, reach_receive};
use crate::scheduler_hooks::YIELD_PTR;
use crate::term::{NumericMode, TermComparator};
use crate::{write_output, write_warning};
use std::slice::from_raw_parts;
use std::sync::atomic::{AtomicU64, Ordering};
use unicode_segmentation::GraphemeCursor;

fn any_value_ref_from_word(word: u64, context: &str) -> AnyValueRef {
    AnyValueRef::from_raw_word(word).unwrap_or_else(|err| panic!("{context}: invalid any value ref {word:#x}: {err:?}"))
}

fn any_value_from_ref_word(word: u64, context: &str) -> AnyValue {
    AnyValue::from_ref(any_value_ref_from_word(word, context)).expect(context)
}

fn heap_ref_word(tag: ValueKind, addr: *const u8) -> u64 {
    AnyValueRef::from_heap_object(tag, addr)
        .expect("heap object ref")
        .raw_word()
}

fn closure_ref_word_from_bits(bits: u64) -> u64 {
    let addr = closure_addr_from_tagged(bits).expect("closure heap bits");
    heap_ref_word(ValueKind::CLOSURE, addr)
}

fn closure_ref_from_word(word: u64, context: &str) -> AnyValueRef {
    let closure = any_value_ref_from_word(word, context);
    closure.closure_addr().expect(context);
    closure
}

fn closure_addr_from_ref_word(word: u64, context: &str) -> *mut u8 {
    any_value_ref_from_word(word, context).closure_addr().expect(context)
}

fn map_ref_word_from_bits(bits: u64) -> u64 {
    let addr = map_addr_from_tagged(bits).expect("map heap bits");
    heap_ref_word(ValueKind::MAP, addr)
}

fn process_atom_id(process: *mut Process, name: &str) -> u32 {
    // Intern into the node-global atom table (shared, append-only): a
    // runtime-created atom gets the same id in every process on this node.
    unsafe { (*process).node.intern_atom(name) }
}

fn alloc_stat_entries(process: *mut Process, entries: &mut Vec<(AnyValue, AnyValue)>, prefix: &str, stat: AllocStat) {
    let allocs_key = process_atom_id(process, &format!("{prefix}_allocs"));
    let bytes_key = process_atom_id(process, &format!("{prefix}_bytes"));
    entries.push((AnyValue::atom(allocs_key), AnyValue::int(stat.allocs as i64)));
    entries.push((AnyValue::atom(bytes_key), AnyValue::int(stat.bytes as i64)));
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_system_alloc_stats(process: *mut Process) -> u64 {
    let p = unsafe { &mut *process };
    let snapshot = p.node.alloc_stats();
    let scheduler_yields = p.scheduler_yields;
    let interpreter_yields = p.interpreter_yields;
    let reductions_remaining = p.reductions_remaining;
    let reductions_per_quantum = p.reductions_per_quantum;
    let reductions_executed = p.reductions_executed;
    let reduction_yields = p.reduction_yields;
    let yield_reasons = p.yield_reasons;
    let max_yield_continuation_bytes = p.max_yield_continuation_bytes;
    let min_yield_continuation_margin_before_bytes = p.min_yield_continuation_margin_before_bytes;
    let min_yield_continuation_margin_after_bytes = p.min_yield_continuation_margin_after_bytes;
    let mut entries = Vec::with_capacity(32);
    entries.push((
        AnyValue::atom(process_atom_id(process, "allocs")),
        AnyValue::int(snapshot.total.allocs as i64),
    ));
    entries.push((
        AnyValue::atom(process_atom_id(process, "bytes")),
        AnyValue::int(snapshot.total.bytes as i64),
    ));
    alloc_stat_entries(process, &mut entries, "list_cons", snapshot.list_cons);
    alloc_stat_entries(process, &mut entries, "struct", snapshot.struct_);
    alloc_stat_entries(process, &mut entries, "closure", snapshot.closure);
    alloc_stat_entries(process, &mut entries, "continuation", snapshot.continuation);
    alloc_stat_entries(process, &mut entries, "map", snapshot.map);
    alloc_stat_entries(process, &mut entries, "bitstring", snapshot.bitstring);
    alloc_stat_entries(process, &mut entries, "binview", snapshot.binview);
    alloc_stat_entries(process, &mut entries, "binref", snapshot.binref);
    alloc_stat_entries(process, &mut entries, "shared_bin", snapshot.shared_bin);
    alloc_stat_entries(process, &mut entries, "scalar_box", snapshot.scalar_box);
    alloc_stat_entries(process, &mut entries, "resource", snapshot.resource);
    alloc_stat_entries(process, &mut entries, "other", snapshot.other);
    entries.push((
        AnyValue::atom(process_atom_id(process, "scheduler_yields")),
        AnyValue::int(scheduler_yields as i64),
    ));
    entries.push((
        AnyValue::atom(process_atom_id(process, "interpreter_yields")),
        AnyValue::int(interpreter_yields as i64),
    ));
    entries.push((
        AnyValue::atom(process_atom_id(process, "reductions_remaining")),
        AnyValue::int(reductions_remaining as i64),
    ));
    entries.push((
        AnyValue::atom(process_atom_id(process, "reductions_per_quantum")),
        AnyValue::int(reductions_per_quantum as i64),
    ));
    entries.push((
        AnyValue::atom(process_atom_id(process, "reductions_executed")),
        AnyValue::int(reductions_executed as i64),
    ));
    entries.push((
        AnyValue::atom(process_atom_id(process, "reduction_yields")),
        AnyValue::int(reduction_yields as i64),
    ));
    entries.push((
        AnyValue::atom(process_atom_id(process, "yield_reasons")),
        AnyValue::int(yield_reasons as i64),
    ));
    entries.push((
        AnyValue::atom(process_atom_id(process, "max_yield_continuation_bytes")),
        AnyValue::int(max_yield_continuation_bytes as i64),
    ));
    entries.push((
        AnyValue::atom(process_atom_id(process, "min_yield_continuation_margin_before_bytes")),
        AnyValue::int(min_yield_continuation_margin_before_bytes as i64),
    ));
    entries.push((
        AnyValue::atom(process_atom_id(process, "min_yield_continuation_margin_after_bytes")),
        AnyValue::int(min_yield_continuation_margin_after_bytes as i64),
    ));
    map_ref_word_from_bits((unsafe { &mut *process }).heap.alloc_map_slots(&entries))
}

/// The heap bits of the unpublished destination a reference names. The null
/// reference is `0`: an update that has missed a key has no destination.
#[inline]
fn destination_bits_from_ref_word(word: u64, context: &str) -> u64 {
    let dest = any_value_ref_from_word(word, context);
    match dest.tag() {
        ValueKind::NULL => 0,
        ValueKind::MAP | ValueKind::STRUCT => dest.raw_word(),
        other => panic!("{context}: {other:?} is no map destination"),
    }
}

/// The reference to the destination `bits` names, null for `0`. A heap
/// object's bits are its reference word.
fn destination_ref_word(bits: u64) -> u64 {
    if bits == 0 {
        AnyValueRef::null().raw_word()
    } else {
        bits
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_type_of(ref_word: u64) -> u8 {
    any_value_ref_from_word(ref_word, "fz_type_of").tag().tag()
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_ref_load_int(ref_word: u64) -> i64 {
    ref_load_int_impl(ref_word)
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_unbox_int(ref_word: u64) -> i64 {
    ref_load_int_impl(ref_word)
}

fn ref_load_int_impl(ref_word: u64) -> i64 {
    any_value_ref_from_word(ref_word, "fz_ref_load_int")
        .load_int()
        .expect("fz_ref_load_int")
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_ref_load_float(ref_word: u64) -> f64 {
    ref_load_float_impl(ref_word)
}

/// The IEEE 754 bits of the number a ref names as an f64: a float's own bits,
/// or an integer's converted value. Nothing is allocated.
#[unsafe(no_mangle)]
pub extern "C" fn fz_number_ref_float_bits(ref_word: u64) -> i64 {
    let value = any_value_from_ref_word(ref_word, "fz_number_ref_float_bits");
    match value.kind() {
        ValueKind::FLOAT => value.raw() as i64,
        ValueKind::INT => (value.raw() as i64 as f64).to_bits() as i64,
        _ => panic!("float bit field expects Int or Float"),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_unbox_float(ref_word: u64) -> f64 {
    ref_load_float_impl(ref_word)
}

fn ref_load_float_impl(ref_word: u64) -> f64 {
    any_value_ref_from_word(ref_word, "fz_ref_load_float")
        .load_float()
        .expect("fz_ref_load_float")
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_ref_load_atom(ref_word: u64) -> u64 {
    ref_load_atom_impl(ref_word)
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_unbox_atom(ref_word: u64) -> u64 {
    ref_load_atom_impl(ref_word)
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_struct_schema_id_ref(ref_word: u64) -> u32 {
    let addr = any_value_ref_from_word(ref_word, "fz_struct_schema_id_ref")
        .struct_addr()
        .expect("fz_struct_schema_id_ref");
    unsafe { struct_schema_id(addr.cast_const()) }
}

/// Whether the struct `ref_word` names is a named struct, and so a map.
#[unsafe(no_mangle)]
pub extern "C" fn fz_struct_is_named_ref(ref_word: u64) -> u8 {
    let addr = any_value_ref_from_word(ref_word, "fz_struct_is_named_ref")
        .struct_addr()
        .expect("fz_struct_is_named_ref");
    u8::from(unsafe { struct_is_named(addr.cast_const()) })
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_truthy_ref(ref_word: u64) -> u8 {
    let value = any_value_ref_from_word(ref_word, "fz_truthy_ref");
    if value.tag() != ValueKind::ATOM {
        return 1;
    }
    let atom = value.load_atom().expect("fz_truthy_ref atom");
    (atom != FALSE_ATOM_ID as u64 && atom != NIL_ATOM_ID as u64) as u8
}

fn ref_load_atom_impl(ref_word: u64) -> u64 {
    any_value_ref_from_word(ref_word, "fz_ref_load_atom")
        .load_atom()
        .expect("fz_ref_load_atom")
}

fn box_scalar_for_any(process: *mut Process, raw: u64, tag: ValueKind) -> u64 {
    (unsafe { &mut *process })
        .heap
        .box_any_value_ref(AnyValue::decode_parts(raw, tag.tag()).expect("scalar value"))
        .raw_word()
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_box_opaque_for_any(process: *mut Process, raw: u64, kind: u64) -> u64 {
    box_scalar_for_any(process, raw, ValueKind::new(kind as u8).expect("opaque word kind"))
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_unbox_opaque(ref_word: u64, kind: u64) -> u64 {
    let kind = ValueKind::new(kind as u8).expect("opaque word kind");
    any_value_ref_from_word(ref_word, "fz_unbox_opaque")
        .load_opaque_word(kind)
        .unwrap_or_else(|err| panic!("fz_unbox_opaque: {err:?}"))
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_box_int_for_any(process: *mut Process, raw: i64) -> u64 {
    box_scalar_for_any(process, raw as u64, ValueKind::INT)
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_box_float_for_any(process: *mut Process, raw: f64) -> u64 {
    box_scalar_for_any(process, raw.to_bits(), ValueKind::FLOAT)
}

// ===== Halt + print cluster =====

/// `IO.write/1`'s only output: the bytes of a byte-aligned binary, exactly as
/// given, to the process's output hook. Declared `unit`: the `IO` wrappers
/// answer `:ok` themselves, so a print allocates nothing.
#[unsafe(no_mangle)]
pub extern "C" fn fz_io_write(process: *mut Process, binary_ref: u64) -> u64 {
    write_output(process, unsafe { Bin::of_binary(binary_ref) }.bytes());
    0
}

/// `IO.warn`'s only output: a message, and the file and line it points at
/// (an empty file is no location), to the process's warning hook.
#[unsafe(no_mangle)]
pub extern "C" fn fz_io_warn(process: *mut Process, message_ref: u64, file_ref: u64, line: i64) -> u64 {
    let message = unsafe { Bin::of_binary(message_ref) }.bytes();
    let file = unsafe { Bin::of_binary(file_ref) }.bytes();
    write_warning(
        process,
        message.as_ptr(),
        message.len(),
        file.as_ptr(),
        file.len(),
        u32::try_from(line).unwrap_or(0),
    );
    0
}

/// `Macro.expand_once/2` of a macro call, asked of the compiler a macro body
/// runs inside: `[code]` or `[code, expanded]` with the code of
/// `output::Expansion` (`NO_COMPILER_CODE` when no compiler runs). The compiler answers
/// from its own scope, so the call is an AST node and the context says
/// whether it stands in an expression (0), a pattern (1) or a guard (2).
#[unsafe(no_mangle)]
pub extern "C" fn fz_macro_expand(process: *mut Process, ast_ref: u64, context: i64) -> u64 {
    let (code, expanded) = crate::request_expansion(process, ast_ref, context);
    let process = unsafe { &mut *process };
    let tail = if code == crate::output::Expansion::EXPANDED_CODE {
        let expanded = any_value_from_ref_word(expanded, "fz_macro_expand");
        process.heap.alloc_list_cons_any(expanded, AnyValue::EmptyList)
    } else {
        AnyValueRef::empty_list()
    };
    let code = i64::try_from(code).expect("an expansion code is small");
    process
        .heap
        .alloc_list_cons_int(code, tail)
        .expect("fz_macro_expand list")
        .raw_word()
}

/// Typed halt for narrow-int seams. The cont chain
/// carries a raw i64 all the way to halt-cont's RawInt body; no
/// unboxing — value is already a machine int.
#[unsafe(no_mangle)]
pub extern "C" fn fz_halt_implicit_i64(process: *mut Process, val: i64) {
    (unsafe { &mut *process }).halt_value = val;
}

/// Typed halt for narrow-float seams. Mirrors
/// fz_halt's Boxed-float branch: store `to_bits() as i64` so tests
/// can round-trip via f64::from_bits.
#[unsafe(no_mangle)]
pub extern "C" fn fz_halt_implicit_f64(process: *mut Process, val: f64) {
    (unsafe { &mut *process }).halt_value = val.to_bits() as i64;
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_halt_implicit_atom(process: *mut Process, atom_id: u64) {
    (unsafe { &mut *process }).halt_value = atom_id as i64;
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_halt_implicit_ref(process: *mut Process, ref_word: u64) {
    (unsafe { &mut *process }).halt_value =
        halt_value_from_slot(any_value_from_ref_word(ref_word, "fz_halt_implicit_ref"));
}

fn halt_value_from_slot(value: AnyValue) -> i64 {
    match value.kind() {
        ValueKind::INT => value.raw() as i64,
        ValueKind::ATOM => value.raw() as i64,
        ValueKind::FLOAT => value.raw() as i64,
        ValueKind::NULL => 0,
        kind if kind.is_heap() => value.heap_object_word().unwrap_or(value.raw()) as i64,
        _ => value.raw() as i64,
    }
}

// ===== Concurrency cluster =====

/// Scheduler-bound builtins.
///
/// Both dispatch through the scheduler callbacks installed on the current
/// process's execution context. Calling either without that context panics.
///
/// Borrow the execution context a BIF reaches scheduler services through.
/// The owning scheduler installs it on the Process (`ctx.2`); it outlives any
/// FFI call made under this process.
#[inline]
unsafe fn process_ctx<'a>(process: *mut Process) -> &'a ExecCtx {
    let ctx = unsafe { (*process).ctx };
    debug_assert!(!ctx.is_null(), "process.ctx installed before BIF dispatch");
    unsafe { &*ctx }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_spawn(process: *mut Process, closure_ref_word: u64) -> u64 {
    let ctx = unsafe { process_ctx(process) };
    (ctx.spawn.expect("spawn callback installed"))(process, ctx.scheduler, closure_ref_word) as u64
}

/// Allocate a resource on the current process heap whose destructor is the
/// literal closure `dtor_ref`. The resource keeps the closure's ref word and
/// the scheduler runs it with the payload when the last stub dies. A literal
/// closure lives outside every heap, so no collection moves or frees it. A
/// capturing closure is on a heap and is refused: the result is `nil`, an atom
/// ref that is never a resource ref, which `Kernel.make_resource` raises as an
/// `ArgumentError`. This is the one place that decides the destructor is
/// literal.
#[unsafe(no_mangle)]
pub extern "C" fn fz_make_resource(process: *mut Process, payload_raw: u64, dtor_ref: u64) -> u64 {
    assert!(!process.is_null(), "fz_make_resource: no current process");
    let dtor_ref = any_value_ref_from_word(dtor_ref, "fz_make_resource destructor");
    assert!(
        dtor_ref.closure_addr().is_ok(),
        "fz_make_resource: destructor is not a closure"
    );
    if !dtor_ref.is_literal() {
        return nil_atom_ref().raw_word();
    }
    let handle = ResourceHandle::new(payload_raw, dtor_ref.raw_word());
    let stub = alloc_resource(&mut unsafe { &mut *process }.heap, handle);
    AnyValueRef::from_heap_object(ValueKind::RESOURCE, stub.as_raw() as *const u8)
        .expect("fz_make_resource: resource ref")
        .raw_word()
}

/// Atomically claims a resource's payload for deterministic cleanup. The
/// caller must read the payload before claiming it; a false result means an
/// alias has already claimed the shared capability.
#[unsafe(no_mangle)]
pub extern "C" fn fz_resource_claim(process: *mut Process, resource_ref_word: u64) -> u64 {
    assert!(!process.is_null(), "fz_resource_claim: no current process");
    let resource = any_value_ref_from_word(resource_ref_word, "fz_resource_claim resource");
    let stub = unsafe { ResourceStub::from_raw(resource.resource_addr().expect("fz_resource_claim resource")) };
    u64::from(stub.claim())
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_self(process: *mut Process) -> u64 {
    (unsafe { &mut *process }).pid as u64
}

/// Process-global monotonic counter feeding `fz_make_ref` and
/// `fz_unique_integer`.
/// Starts at 1 so 0 can remain a "no ref" sentinel if a future ticket
/// needs one. AtomicU64 + Relaxed is sufficient under single-worker
/// today and remains correct under future multi-worker.
static FZ_NEXT_REF: AtomicU64 = AtomicU64::new(1);

#[unsafe(no_mangle)]
pub extern "C" fn fz_make_ref() -> u64 {
    FZ_NEXT_REF.fetch_add(1, Ordering::Relaxed)
}

/// `:erlang.unique_integer/0`: an integer no other call in this run returns,
/// drawn from the counter references are drawn from.
#[unsafe(no_mangle)]
pub extern "C" fn fz_unique_integer() -> i64 {
    FZ_NEXT_REF.fetch_add(1, Ordering::Relaxed) as i64
}

/// fz_send(receiver_pid, msg_ref) -> msg_ref.
///
/// `send` is an `any` boundary: callers box known scalars before calling, then
/// the scheduler/mailbox moves the one-word any value ref until a matcher or
/// receiver unwraps it.
#[unsafe(no_mangle)]
pub extern "C" fn fz_send(process: *mut Process, receiver_pid_bits: u64, msg_ref_word: u64) -> u64 {
    let receiver_pid = receiver_pid_bits as u32;
    let _ = any_value_ref_from_word(msg_ref_word, "fz_send message");
    let ctx = unsafe { process_ctx(process) };
    (ctx.send.expect("send callback installed"))(process, ctx.scheduler, receiver_pid, msg_ref_word);
    msg_ref_word
}

/// Make room for a `try`'s handler record when the handler stack is full:
/// grow it and reserve `bytes` on top, answering where they start. Compiled
/// code reserves inline while the stack has room and calls this only at its
/// end; either way it then writes the record, trailer last.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_handler_reserve(process: *mut Process, bytes: u64) -> u64 {
    unsafe { &mut *process }.handlers.reserve(bytes as usize) as u64
}

/// Selective receive entry. Generated code calls it where a `receive` is
/// reached, with the site's constant record and the frame this arrival built.
///
/// Args:
/// - `site`: the receive's `ReceiveSite`, emitted once by codegen.
/// - `frame_bits`: the frame closure, `[outer_cont, captures..., pinned...]`.
/// - `after_ms_or_neg1`: the `after` timeout as a relative duration in
///   millis, or `-1` when there is no after (no timer; matcher hit is the
///   only way the receiver wakes).
///
/// The receive is decided here (`sched::reach_receive`): a message that
/// matches, or an `after 0` with nothing matching, returns the closure ref
/// word to run next; a miss that must wait returns the YIELD sentinel so the
/// trampoline parks the task.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_receive_park_matched(
    process: *mut Process,
    site: *const ReceiveSite,
    frame_bits: u64,
    after_ms_or_neg1: i64,
) -> *mut u8 {
    let park = ParkRecord {
        // SAFETY: codegen passes the address of a read-only site record that lives as long as the program.
        site: unsafe { &*site },
        frame: closure_ref_from_word(frame_bits, "fz_receive_park_matched frame"),
        after_deadline_ms: u64::try_from(after_ms_or_neg1).ok(),
        after_timer_id: None,
    };
    let p = unsafe { &mut *process };
    match reach_receive(p, park) {
        ReceiveStep::Continue(closure) => closure.raw_word() as *mut u8,
        ReceiveStep::Parked => YIELD_PTR as *mut u8,
    }
}

/// A pinned value of a receive's frame, as a value ref word. A receive matcher
/// calls it for each value its patterns pin. The frame is
/// `[outer_cont, captures..., pinned...]`, so `from_end` counts the pinned values
/// from the last capture: `1` is the last pinned value.
#[unsafe(no_mangle)]
pub extern "C" fn fz_receive_pinned_ref(frame_bits: u64, from_end: u64) -> u64 {
    let frame = closure_ref_from_word(frame_bits, "fz_receive_pinned_ref frame");
    let addr = frame.closure_addr().expect("a receive frame is a closure ref");
    // SAFETY: the frame is a live closure its arrival holds, and `from_end` names one of its pinned captures.
    unsafe {
        let captured = closure_captured_count(addr);
        closure_capture_ref_word(addr, captured - from_end as usize)
    }
}

/// Boundary-reporting mid-flight yield entry.
///
/// Generated/interpreted code reports the scheduler continuation, signed
/// reductions left in the turn, and the reason bits that caused the yield. The
/// scheduler knows how many reductions it granted, so it derives burned work at
/// the boundary instead of syncing against the hot-path budget cell.
#[unsafe(no_mangle)]
pub extern "C" fn fz_yield_mid_flight_report(
    process: *mut Process,
    cont_closure_bits: u64,
    remaining_reductions: i32,
    reason: u32,
) -> *mut u8 {
    let p = unsafe { &mut *process };
    p.scheduler_yields = p.scheduler_yields.saturating_add(1);
    // Allocation-pressure reasons already stand on `p.yield_reasons`;
    // finish_yield_report folds them in when attributing the cause.
    p.finish_yield_report(remaining_reductions, reason as u8);
    let closure = closure_ref_from_word(cont_closure_bits, "fz_yield_mid_flight_report cont");
    let continuation_bytes = object_size(closure.raw_word());
    let margin_after = p.heap.bytes_remaining_in_block();
    p.note_yield_continuation_allocation(continuation_bytes, margin_after);
    p.set_runnable_closure(closure);
    YIELD_PTR as *mut u8
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_yield_slow_path_begin(process: *mut Process) {
    let p = unsafe { &mut *process };
    p.begin_yield_continuation_allocation(p.heap.bytes_remaining_in_block());
}

// ===== Closure cluster =====
//
// Closures carry source denotation, a self-describing environment, and code at +8.
// Invocation is a call_indirect through that code pointer; captures are
// ordinary env fields read and written through the runtime accessors.

/// Room for `size` bytes (a multiple of 16) beyond a full tip block, for the
/// inline bump of compiled code: the address the object starts at, in a fresh
/// tip or, for a huge object, in a block of its own. Nothing is written into
/// the object; compiled code writes it.
#[unsafe(no_mangle)]
pub extern "C" fn fz_heap_room(process: *mut Process, size: usize) -> *mut u8 {
    (unsafe { &mut *process }).heap.room(size)
}

/// The body frame a write goes to: `frame` itself when it is young, else a copy
/// of it at the heap tip. A collection keeps its survivors in old blocks, and a
/// write into one that names a younger object is invisible to the next minor
/// collection; the copy is young, and the frame it replaces is dead. Every
/// slot and kind byte is copied, so the copy resumes where the original would
/// have. Compiled code asks only when the frame lies outside the tip block;
/// a frame parked alone in a young block of its own is answered as it is.
#[unsafe(no_mangle)]
pub extern "C" fn fz_frame_for_write(process: *mut Process, frame: u64) -> u64 {
    let frame_ref = any_value_ref_from_word(frame, "fz_frame_for_write frame");
    let src = frame_ref.closure_addr().expect("fz_frame_for_write frame");
    let process = unsafe { &mut *process };
    if !frame_ref.is_literal() && crate::heap::arena::range().is_young(src) {
        return frame;
    }
    let count = unsafe { crate::any_value::closure_captured_count(src) };
    process.frame_copies += 1;
    let bits = process.heap.alloc_continuation_slots(1, count);
    let dst = closure_addr_from_tagged(bits).expect("copied frame bits");
    unsafe { std::ptr::copy_nonoverlapping(src, dst, crate::any_value::closure_size_for_count(count)) };
    closure_ref_word_from_bits(bits)
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_closure_code_ref(closure_ref_word: u64) -> u64 {
    let addr = closure_addr_from_ref_word(closure_ref_word, "fz_closure_code_ref closure");
    unsafe { closure_fn_ptr(addr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_closure_halt_kind_ref(closure_ref_word: u64) -> u32 {
    let addr = closure_addr_from_ref_word(closure_ref_word, "fz_closure_halt_kind_ref closure");
    unsafe { closure_halt_kind(addr) as u32 }
}

// ===== Bitstring cluster =====

/// Build a binary from `count` segments at `fields`: sized first, allocated
/// once, each segment written once. See [`crate::construction`].
#[unsafe(no_mangle)]
pub extern "C" fn fz_bs_build(process: *mut Process, fields: *const FzBsField, count: u64) -> u64 {
    // SAFETY: the caller passes `count` descriptors that stay valid for the call.
    let fields = unsafe { from_raw_parts(fields, count as usize) };
    construction::build(unsafe { &mut *process }, fields)
}

/// A binary of `byte_len` whole bytes whose payload the caller writes, on the
/// path of a construction the compiled code fills itself. See
/// [`crate::construction::alloc_unfilled`].
#[unsafe(no_mangle)]
pub extern "C" fn fz_bs_alloc_unfilled(process: *mut Process, byte_len: u64) -> u64 {
    construction::alloc_unfilled(unsafe { &mut *process }, byte_len as usize)
}

/// The binary `leading` followed by `right_len` bytes the caller writes, on the
/// path of an append the compiled code fills itself. See
/// [`crate::construction::append_unfilled`].
#[unsafe(no_mangle)]
pub extern "C" fn fz_bs_append_unfilled(process: *mut Process, leading: u64, right_len: u64) -> u64 {
    construction::append_unfilled(unsafe { &mut *process }, leading, right_len as usize)
}

/// A total integer arithmetic result returned by value at the C boundary.
/// `failed` is a canonical `u64` 0 or 1, deliberately not Rust `bool`.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FzIntegerArithmeticResult {
    pub result: i64,
    pub failed: u64,
}

/// A total floating arithmetic result returned by value at the C boundary.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FzFloatArithmeticResult {
    pub result: f64,
    pub failed: u64,
}

fn successful_integer(result: i64) -> FzIntegerArithmeticResult {
    FzIntegerArithmeticResult { result, failed: 0 }
}

fn failed_integer(result: i64) -> FzIntegerArithmeticResult {
    FzIntegerArithmeticResult { result, failed: 1 }
}

fn finite_float(result: f64) -> FzFloatArithmeticResult {
    if result.is_finite() {
        FzFloatArithmeticResult { result, failed: 0 }
    } else {
        FzFloatArithmeticResult { result: 0.0, failed: 1 }
    }
}

/// `/` on two integers, which is a FLOAT in Elixir: `1 / 2` is `0.5`, not `0`.
/// Division by either signed zero stays total and returns `{0.0, 1}`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_op_div_ii_to_float(a: i64, b: i64) -> FzFloatArithmeticResult {
    finite_float(a as f64 / b as f64)
}

/// Wrapped bits remain observable alongside the overflow status.
#[unsafe(no_mangle)]
pub extern "C" fn fz_op_neg_i(value: i64) -> FzIntegerArithmeticResult {
    let (result, overflowed) = value.overflowing_neg();
    FzIntegerArithmeticResult {
        result,
        failed: u64::from(overflowed),
    }
}

/// Bitwise AND of two integers, as two's complement bits.
#[unsafe(no_mangle)]
pub extern "C" fn fz_op_band_ii(left: i64, right: i64) -> i64 {
    left & right
}

/// Bitwise OR of two integers, as two's complement bits.
#[unsafe(no_mangle)]
pub extern "C" fn fz_op_bor_ii(left: i64, right: i64) -> i64 {
    left | right
}

/// Bitwise exclusive OR of two integers, as two's complement bits.
#[unsafe(no_mangle)]
pub extern "C" fn fz_op_bxor_ii(left: i64, right: i64) -> i64 {
    left ^ right
}

/// Bitwise complement: `-value - 1`, which every 64-bit integer has.
#[unsafe(no_mangle)]
pub extern "C" fn fz_op_bnot_i(value: i64) -> i64 {
    !value
}

/// `value` shifted right by `count` bits, which keeps the sign. A count past
/// the width shifts out every bit but the sign.
fn shifted_right(value: i64, count: u64) -> FzIntegerArithmeticResult {
    successful_integer(value >> count.min(u64::from(i64::BITS - 1)))
}

/// `value` shifted left by `count` bits. The shift fails when the shifted bits
/// no longer fit a 64-bit integer, where Elixir would grow a bignum. The
/// wrapped bits stay observable beside the failure, as in `fz_op_neg_i`.
fn shifted_left(value: i64, count: i64) -> FzIntegerArithmeticResult {
    let wrapped = value.wrapping_shl(count as u32);
    let in_range = (count as u64) < u64::from(i64::BITS);
    let fits = value == 0 || (in_range && wrapped.wrapping_shr(count as u32) == value);
    FzIntegerArithmeticResult {
        result: wrapped,
        failed: u64::from(!fits),
    }
}

/// `bsl`: a negative `count` shifts right. Fails when the result needs more
/// than 64 bits.
#[unsafe(no_mangle)]
pub extern "C" fn fz_op_bsl_ii(value: i64, count: i64) -> FzIntegerArithmeticResult {
    if count < 0 {
        shifted_right(value, count.unsigned_abs())
    } else {
        shifted_left(value, count)
    }
}

/// `bsr`: an arithmetic shift right, which keeps the sign. A negative `count`
/// shifts left and fails when the result needs more than 64 bits.
#[unsafe(no_mangle)]
pub extern "C" fn fz_op_bsr_ii(value: i64, count: i64) -> FzIntegerArithmeticResult {
    if count >= 0 {
        shifted_right(value, count as u64)
    } else {
        shifted_left(value, count.wrapping_neg())
    }
}

/// `fneg` flips the sign bit, so `-0.0` stays `-0.0`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_op_neg_f(value: f64) -> f64 {
    -value
}

/// `abs` of the minimum integer has no 64-bit answer, so it reports failure.
#[unsafe(no_mangle)]
pub extern "C" fn fz_op_abs_i(value: i64) -> FzIntegerArithmeticResult {
    let (result, overflowed) = value.overflowing_abs();
    FzIntegerArithmeticResult {
        result,
        failed: u64::from(overflowed),
    }
}

/// `abs` clears the sign bit, so `-0.0` becomes `0.0`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_op_abs_f(value: f64) -> f64 {
    value.abs()
}

/// An already-rounded float as an integer, or a failure when it lies outside
/// the 64-bit range. The bounds are exact powers of two, so each is a float.
fn rounded_float_as_integer(rounded: f64) -> FzIntegerArithmeticResult {
    const LOWER: f64 = -9223372036854775808.0;
    const UPPER: f64 = 9223372036854775808.0;
    if (LOWER..UPPER).contains(&rounded) {
        successful_integer(rounded as i64)
    } else {
        failed_integer(0)
    }
}

/// Rounds half away from zero, as Elixir's `round/1` does.
#[unsafe(no_mangle)]
pub extern "C" fn fz_op_round_f(value: f64) -> FzIntegerArithmeticResult {
    rounded_float_as_integer(value.round())
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_op_trunc_f(value: f64) -> FzIntegerArithmeticResult {
    rounded_float_as_integer(value.trunc())
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_op_floor_f(value: f64) -> FzIntegerArithmeticResult {
    rounded_float_as_integer(value.floor())
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_op_ceil_f(value: f64) -> FzIntegerArithmeticResult {
    rounded_float_as_integer(value.ceil())
}

macro_rules! integer_arithmetic_export {
    ($name:ident, $method:ident) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn $name(left: i64, right: i64) -> FzIntegerArithmeticResult {
            let (result, overflowed) = left.$method(right);
            FzIntegerArithmeticResult {
                result,
                failed: u64::from(overflowed),
            }
        }
    };
}

integer_arithmetic_export!(fz_op_add_ii, overflowing_add);
integer_arithmetic_export!(fz_op_sub_ii, overflowing_sub);
integer_arithmetic_export!(fz_op_mul_ii, overflowing_mul);

macro_rules! float_arithmetic_export {
    ($name:ident, ($left:ident : $left_ty:ty, $right:ident : $right_ty:ty) => $expression:expr) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn $name($left: $left_ty, $right: $right_ty) -> FzFloatArithmeticResult {
            finite_float($expression)
        }
    };
}

float_arithmetic_export!(fz_op_add_if, (left: i64, right: f64) => left as f64 + right);
float_arithmetic_export!(fz_op_add_ff, (left: f64, right: f64) => left + right);
float_arithmetic_export!(fz_op_sub_if, (left: i64, right: f64) => left as f64 - right);
float_arithmetic_export!(fz_op_sub_fi, (left: f64, right: i64) => left - right as f64);
float_arithmetic_export!(fz_op_sub_ff, (left: f64, right: f64) => left - right);
float_arithmetic_export!(fz_op_mul_if, (left: i64, right: f64) => left as f64 * right);
float_arithmetic_export!(fz_op_mul_ff, (left: f64, right: f64) => left * right);

/// Guard both hardware integer-division trap cases before evaluating `/`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_op_div_ii(left: i64, right: i64) -> FzIntegerArithmeticResult {
    if right == 0 || (left == i64::MIN && right == -1) {
        failed_integer(0)
    } else {
        successful_integer(left / right)
    }
}

float_arithmetic_export!(fz_op_div_if, (left: i64, right: f64) => left as f64 / right);
float_arithmetic_export!(fz_op_div_fi, (left: f64, right: i64) => left / right as f64);
float_arithmetic_export!(fz_op_div_ff, (left: f64, right: f64) => left / right);

/// `MIN_I64 rem -1` is a successful zero even though its quotient overflows.
#[unsafe(no_mangle)]
pub extern "C" fn fz_op_rem_ii(left: i64, right: i64) -> FzIntegerArithmeticResult {
    if right == 0 {
        failed_integer(0)
    } else if left == i64::MIN && right == -1 {
        successful_integer(0)
    } else {
        successful_integer(left % right)
    }
}

// Float remainder uses fmod-compatible `%`; it remains a helper call in
// optimized code because Cranelift has no `frem` instruction.
float_arithmetic_export!(fz_op_rem_if, (left: i64, right: f64) => left as f64 % right);
float_arithmetic_export!(fz_op_rem_fi, (left: f64, right: i64) => left % right as f64);
float_arithmetic_export!(fz_op_rem_ff, (left: f64, right: f64) => left % right);

/// Unicode simple case mapping, the table `String.upcase/1` needs.
///
/// A TABLE, not an algorithm, and it lives here rather than in fz source for a
/// reason worth stating: Elixir generates about 2,989 clauses from
/// UnicodeData.txt, and 2,723 fz clauses would put that table through the
/// dispatch matrix -- compile work proportional to the TABLE rather than to the
/// program, which is the opposite of what fz is for. Encoding it as a literal
/// binary and binary-searching it keeps the clause count at one but costs an
/// allocation per character.
///
/// The ticket's design goal survives the move: it asked for ONE coherent
/// Unicode version, which Elixir cannot have because its case mapping and
/// OTP's grapheme breaking track different releases. Rust's `char` tables are
/// one version, and `fz_grapheme_size` draws grapheme breaking from the
/// `unicode-segmentation` tables at that same version.
///
/// FULL casing, which is Elixir's default mode: the 103 special casings expand
/// one codepoint to several, so `"straße"` upcases to `"STRASSE"`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_binary_upcase(process: *mut Process, ref_word: u64) -> u64 {
    map_case(process, ref_word, true)
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_binary_downcase(process: *mut Process, ref_word: u64) -> u64 {
    map_case(process, ref_word, false)
}

fn map_case(process: *mut Process, ref_word: u64, upper: bool) -> u64 {
    let bytes = unsafe { Bin::of_binary(ref_word) }.bytes();
    let Ok(text) = std::str::from_utf8(bytes) else {
        panic!("case mapping expects valid UTF-8");
    };
    let mut out = String::with_capacity(text.len());
    for ch in text.chars() {
        // Full casing rather than simple: `to_uppercase` yields several
        // codepoints for the special casings, and taking all of them is what
        // makes `"straße"` upcase to `"STRASSE"`, the way Elixir's default
        // mode does.
        if upper {
            out.extend(ch.to_uppercase());
        } else {
            out.extend(ch.to_lowercase());
        }
    }
    alloc_text(process, &out)
}

/// The byte length of the first extended grapheme cluster of a binary.
///
/// Only the valid UTF-8 prefix is segmented, so a cluster never runs across an
/// invalid byte; a binary that starts with an invalid byte has that one byte as
/// its first grapheme, which is what Elixir does.
#[unsafe(no_mangle)]
pub extern "C" fn fz_grapheme_size(_process: *mut Process, ref_word: u64) -> i64 {
    let bytes = unsafe { Bin::of_binary(ref_word) }.bytes();
    let valid = match std::str::from_utf8(bytes) {
        Ok(text) => text,
        Err(e) => std::str::from_utf8(&bytes[..e.valid_up_to()]).expect("prefix is valid by construction"),
    };
    if valid.is_empty() {
        return 1;
    }
    let mut cursor = GraphemeCursor::new(0, valid.len(), true);
    let boundary = cursor.next_boundary(valid, 0).expect("the whole text is in the chunk");
    boundary.expect("non-empty text has a boundary") as i64
}

/// Whether a binary is a valid UTF-8 string of printable codepoints: the
/// answer `String.printable?/1` gives, and the one `inspect` uses to choose a
/// quoted string over `<<...>>`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_binary_printable(_process: *mut Process, ref_word: u64) -> u64 {
    let bytes = unsafe { Bin::of_binary(ref_word) }.bytes();
    u64::from(std::str::from_utf8(bytes).is_ok_and(crate::any_value::debug::is_printable_utf8))
}

/// Intern a binary as an atom, the way `String.to_atom/1` does.
///
/// Atoms are node-global and never collected, which is why Elixir warns about
/// calling this on untrusted input. The table is the same one compile-time
/// atoms live in, so an atom the program already mentions interns to the id it
/// already has.
#[unsafe(no_mangle)]
pub extern "C" fn fz_binary_to_atom(process: *mut Process, ref_word: u64) -> u64 {
    let bytes = unsafe { Bin::of_binary(ref_word) }.bytes();
    let Ok(name) = std::str::from_utf8(bytes) else {
        panic!("String.to_atom expects valid UTF-8");
    };
    let id = (unsafe { &*process }).node.intern_atom(name);
    box_scalar_for_any(process, id as u64, ValueKind::ATOM)
}

/// The number of BYTES that hold the bitstring starting `bit_pos` bits into
/// `ref_word`'s bitstring: the whole bitstring at position zero, the rest of it
/// from a cursor. A partial last byte counts, as in Elixir's `byte_size`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_bitstring_byte_extent(ref_word: u64, bit_pos: u64) -> i64 {
    let bit_len = unsafe { Bin::of_binary(ref_word) }.bit_len();
    (bit_len - bit_pos).div_ceil(8) as i64
}

/// The number of bytes that hold a bitstring, a partial last byte counted; -1
/// for any other value, so the question "do `n` bytes hold this value" is total
/// over what it is handed.
#[unsafe(no_mangle)]
pub extern "C" fn fz_bitstring_byte_size_of(_process: *mut Process, value_ref_word: u64) -> i64 {
    if !is_bitstring_like(value_ref_word) {
        return -1;
    }
    fz_bitstring_byte_extent(value_ref_word, 0)
}

/// The number of BITS in the bitstring starting `bit_pos` bits into
/// `ref_word`'s bitstring: the whole bitstring at position zero, the rest of it
/// from a cursor, as in Elixir's `bit_size`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_bitstring_bit_extent(ref_word: u64, bit_pos: u64) -> i64 {
    let bit_len = unsafe { Bin::of_binary(ref_word) }.bit_len();
    (bit_len - bit_pos) as i64
}

/// The size of a `binary` segment whose value is a pinned binary: that binary's
/// byte count, which is what `<<^p::binary, rest::binary>>` reads.
///
/// A pin that is not a binary of whole bytes cannot be a prefix of anything, so
/// it gets a size no subject can hold and the read misses.
#[unsafe(no_mangle)]
pub extern "C" fn fz_pinned_binary_segment_size(ref_word: u64) -> u32 {
    if !is_bitstring_like(ref_word) {
        return u32::MAX;
    }
    let bit_len = unsafe { Bin::of_binary(ref_word) }.bit_len() as usize;
    if !bit_len.is_multiple_of(8) {
        return u32::MAX;
    }
    u32::try_from(bit_len / 8).unwrap_or(u32::MAX)
}

/// Allocate `text` on the process heap as an fz binary.
///
/// The to-string primitives and `fz_inspect` all end here, so the choice between an inline
/// bitstring and a shared binview is made once rather than per primitive.
fn alloc_text(process: *mut Process, text: &str) -> u64 {
    let bytes = text.as_bytes();
    let value = (unsafe { &mut *process }).alloc_bitstring(bytes, (bytes.len() * 8) as u64);
    value.ref_word().raw_word()
}

/// `Atom.to_string/1`: the atom's name, so `:foo` is `"foo"` and `nil` is
/// `"nil"`.
///
/// The `nil -> ""` that Elixir shows belongs to `String.Chars.Atom`, not here
/// (elixir/lib/elixir/lib/string/chars.ex:30) -- `Atom.to_string(nil)` really
/// is `"nil"`. Keeping the special case in the protocol impl means the
/// primitive stays the plain question "what is this atom called".
#[unsafe(no_mangle)]
pub extern "C" fn fz_atom_to_binary(process: *mut Process, atom_ref: u64) -> u64 {
    let value = any_value_ref_from_word(atom_ref, "fz_atom_to_binary");
    let atom_id = value.load_atom().expect("fz_atom_to_binary expects an atom");
    let name = (unsafe { &*process })
        .node
        .atom_name(atom_id as u32)
        .unwrap_or_else(|| panic!("unknown atom id {atom_id}"));
    alloc_text(process, &name)
}

/// `Integer.to_string/1`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_integer_to_binary(process: *mut Process, value: i64) -> u64 {
    alloc_text(process, &value.to_string())
}

/// `Float.to_string/1`, which is not how `inspect/1` renders a float -- see
/// `any_value::debug::float_to_string`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_float_to_binary(process: *mut Process, value: f64) -> u64 {
    alloc_text(process, &crate::any_value::debug::float_to_string(value))
}

/// `:erlang.float_to_binary(x, decimals: n)`: `x` in fixed notation with `n`
/// digits after the point.
#[unsafe(no_mangle)]
pub extern "C" fn fz_float_to_fixed_binary(process: *mut Process, value: f64, decimals: i64) -> u64 {
    let decimals = usize::try_from(decimals).expect("decimals are checked by :erlang.float_to_binary/2");
    alloc_text(process, &fixed_notation(value, decimals))
}

/// More digits than any `f64` has after the point (the smallest subnormal,
/// 2^-1074, has 1074), so Rust prints the value's exact expansion.
const EXACT_FRACTION_DIGITS: usize = 1100;

/// `value` with `decimals` digits after the point, rounded from the float's
/// exact decimal expansion with a tie going away from zero, as Erlang does.
/// Rust's own `{:.n}` breaks a tie to even (`2.5` is `2` at no decimals).
fn fixed_notation(value: f64, decimals: usize) -> String {
    let exact = format!("{:.EXACT_FRACTION_DIGITS$}", value.abs());
    let (whole, fraction) = exact.split_once('.').expect("a fixed-notation float has a point");
    let mut digits: Vec<u8> = whole.bytes().chain(fraction.bytes().take(decimals)).collect();
    if fraction.as_bytes()[decimals] >= b'5' {
        increment_decimal(&mut digits);
    }
    let point = digits.len() - decimals;
    let (whole, fraction) = digits.split_at(point);
    let sign = if value.is_sign_negative() { "-" } else { "" };
    let whole = std::str::from_utf8(whole).expect("ascii digits");
    let fraction = std::str::from_utf8(fraction).expect("ascii digits");
    if decimals == 0 {
        format!("{sign}{whole}")
    } else {
        format!("{sign}{whole}.{fraction}")
    }
}

/// Adds one to the ascii decimal number `digits`, growing it by a digit on
/// overflow.
fn increment_decimal(digits: &mut Vec<u8>) {
    for digit in digits.iter_mut().rev() {
        if *digit == b'9' {
            *digit = b'0';
        } else {
            *digit += 1;
            return;
        }
    }
    digits.insert(0, b'1');
}

/// `Float.parse/1`: `[]` when the binary does not start with a float, else the
/// two-element list `[float, rest]` that the `Float` module builds its tuple from.
///
/// The prefix rules and the rounding live in `float_prefix`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_float_parse(process: *mut Process, binary_ref: u64) -> u64 {
    let bytes = unsafe { Bin::of_binary(binary_ref) }.bytes();
    let Some((float, consumed)) = float_prefix(bytes) else {
        return AnyValueRef::empty_list().raw_word();
    };
    let rest = &bytes[consumed..];
    let process = unsafe { &mut *process };
    let rest_ref = process.alloc_bitstring(rest, (rest.len() * 8) as u64).ref_word();
    let tail = process
        .heap
        .alloc_list_cons_ref(rest_ref, AnyValueRef::empty_list())
        .expect("fz_float_parse tail");
    process
        .heap
        .alloc_list_cons_float(float, tail)
        .expect("fz_float_parse list")
        .raw_word()
}

/// `Macro.unescape_string/1`: `[1, text]` with the escapes of the binary read
/// as Elixir's `unescape_string` reads them, or `[0, message]` when an escape
/// is malformed. Each deprecated escape read is warned about, as `IO.warn`
/// warns. The reading lives in `escape::unescape`, which the lexer's escape
/// reader serves too.
#[unsafe(no_mangle)]
pub extern "C" fn fz_unescape_string(process: *mut Process, binary_ref: u64) -> u64 {
    let bytes = unsafe { Bin::of_binary(binary_ref) }.bytes();
    let (status, answer) = match crate::escape::unescape(bytes) {
        Ok((text, deprecated)) => {
            for escape in deprecated {
                let message = escape.warning();
                write_warning(process, message.as_ptr(), message.len(), b"".as_ptr(), 0, 0);
            }
            (1, text)
        }
        Err(message) => (0, message.into_bytes()),
    };
    let process = unsafe { &mut *process };
    let answer_ref = process.alloc_bitstring(&answer, (answer.len() * 8) as u64).ref_word();
    let tail = process
        .heap
        .alloc_list_cons_ref(answer_ref, AnyValueRef::empty_list())
        .expect("fz_unescape_string tail");
    process
        .heap
        .alloc_list_cons_int(status, tail)
        .expect("fz_unescape_string list")
        .raw_word()
}

unsafe extern "C" {
    fn getline(line: *mut *mut std::ffi::c_char, capacity: *mut usize, stream: *mut std::ffi::c_void) -> isize;
    fn free(ptr: *mut std::ffi::c_void);
    fn fread(buffer: *mut std::ffi::c_void, size: usize, count: usize, stream: *mut std::ffi::c_void) -> usize;
}

/// `File.Stream`'s line reader: `[]` at end of file, else `[line]`, where `line`
/// is the bytes up to and including the next `\n` (or the trailing bytes of a
/// file that does not end in one). A line that ends in `\r\n` comes back
/// ending in `\n`, as Elixir's `File.stream!` reads it; any other `\r` stays.
///
/// `stream` is the C `FILE *` a `File` handle carries. The C library finds the
/// line in its own buffer, and the line is allocated on the heap once.
#[unsafe(no_mangle)]
pub extern "C" fn fz_file_read_line(process: *mut Process, stream: u64) -> u64 {
    let line = read_line_bytes(stream as *mut std::ffi::c_void);
    if line.is_empty() {
        return AnyValueRef::empty_list().raw_word();
    }
    let process = unsafe { &mut *process };
    let line_ref = process.alloc_bitstring(&line, (line.len() * 8) as u64).ref_word();
    process
        .heap
        .alloc_list_cons_ref(line_ref, AnyValueRef::empty_list())
        .expect("fz_file_read_line list")
        .raw_word()
}

/// The bytes of the next line of `stream`, newline included and `\r\n` folded to
/// `\n`; empty at end of file.
fn read_line_bytes(stream: *mut std::ffi::c_void) -> Vec<u8> {
    let mut buffer = std::ptr::null_mut();
    let mut capacity = 0;
    let read = unsafe { getline(&mut buffer, &mut capacity, stream) };
    let mut line = match usize::try_from(read) {
        Ok(len) => unsafe { from_raw_parts(buffer.cast::<u8>(), len) }.to_vec(),
        Err(_) => Vec::new(),
    };
    unsafe { free(buffer.cast()) };
    if line.ends_with(b"\r\n") {
        line.truncate(line.len() - 2);
        line.push(b'\n');
    }
    line
}

/// How many bytes `read_rest_bytes` asks the C library for at a time.
const READ_BLOCK_BYTES: usize = 64 * 1024;

/// `File.read/1`'s reader: every byte of `stream` from its current position to
/// the end of the file, as one binary allocated on the heap once. A read error
/// ends the bytes early; the caller asks `ferror` whether that happened.
///
/// `stream` is the C `FILE *` that `File.read/1` opened.
#[unsafe(no_mangle)]
pub extern "C" fn fz_file_read_rest(process: *mut Process, stream: u64) -> u64 {
    let bytes = read_rest_bytes(stream as *mut std::ffi::c_void);
    let heap = &mut unsafe { &mut *process }.heap;
    heap.alloc_bitstring(&bytes, (bytes.len() * 8) as u64)
        .ref_word()
        .raw_word()
}

/// The bytes of `stream` from its position to the end, read a block at a time
/// into one growing buffer, so the stream need not be seekable or have a
/// known size. A block that comes back short is the end of the file or an
/// error.
fn read_rest_bytes(stream: *mut std::ffi::c_void) -> Vec<u8> {
    let mut bytes = Vec::new();
    loop {
        bytes.reserve(READ_BLOCK_BYTES);
        let room = bytes.spare_capacity_mut().as_mut_ptr().cast();
        let read = unsafe { fread(room, 1, READ_BLOCK_BYTES, stream) };
        unsafe { bytes.set_len(bytes.len() + read) };
        if read < READ_BLOCK_BYTES {
            return bytes;
        }
    }
}

/// The float at the start of `bytes` and how many bytes spell it, or `None`.
///
/// A float is an optional sign, one or more digits, an optional fraction (a
/// `.` and one or more digits) and an optional exponent (`e` or `E`, an
/// optional sign and one or more digits). A `.` or `e` that is not followed by
/// its digits is not part of the number, so `"1."` is `1.0` with `"."` left
/// over. A value too large for a float is `None`, as in Elixir. The text of
/// the prefix is converted by Rust's `f64` parser, which rounds correctly.
fn float_prefix(bytes: &[u8]) -> Option<(f64, usize)> {
    fn digits_from(bytes: &[u8], start: usize) -> usize {
        start
            + bytes[start.min(bytes.len())..]
                .iter()
                .take_while(|b| b.is_ascii_digit())
                .count()
    }
    let sign = usize::from(matches!(bytes.first(), Some(b'+' | b'-')));
    let whole_end = digits_from(bytes, sign);
    if whole_end == sign {
        return None;
    }
    let mut end = whole_end;
    if bytes.get(end) == Some(&b'.') {
        let fraction_end = digits_from(bytes, end + 1);
        if fraction_end > end + 1 {
            end = fraction_end;
        }
    }
    if matches!(bytes.get(end), Some(b'e' | b'E')) {
        let exponent_sign = usize::from(matches!(bytes.get(end + 1), Some(b'+' | b'-')));
        let exponent_end = digits_from(bytes, end + 1 + exponent_sign);
        if exponent_end > end + 1 + exponent_sign {
            end = exponent_end;
        }
    }
    let text = std::str::from_utf8(&bytes[..end]).expect("ASCII prefix");
    let float: f64 = text.parse().expect("a float prefix parses");
    float.is_finite().then_some((float, end))
}

/// The text `inspect/1` gives the value, as a binary: Elixir's default options.
#[unsafe(no_mangle)]
pub extern "C" fn fz_inspect(process: *mut Process, word: u64, kind: u64) -> u64 {
    let value = Stored { word, kind }.value("fz_inspect value");
    alloc_text(process, &render_value(process, value))
}

/// The text `inspect/2` gives the value, as a binary. `options_ref` is the
/// keyword list `Kernel.inspect/2` has already checked: `limit:` and
/// `printable_limit:` are its options.
#[unsafe(no_mangle)]
pub extern "C" fn fz_inspect_with(process: *mut Process, word: u64, kind: u64, options_ref: u64) -> u64 {
    let value = Stored { word, kind }.value("fz_inspect_with value");
    let limits = Limits::from_options(process, any_value_from_ref_word(options_ref, "fz_inspect_with options"));
    alloc_text(process, &render_with_limits(process, value, limits))
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_binary_concat(process: *mut Process, left_ref: u64, right_ref: u64) -> u64 {
    let left = unsafe { Bin::of_binary(left_ref) }.bytes();
    let right = unsafe { Bin::of_binary(right_ref) }.bytes();
    let left_view = binview_addr_from_tagged(left_ref).map(|addr| unsafe { BinView::from_raw(addr) });
    let value = unsafe {
        (&mut *process).alloc_concatenation(left, left_view, right.len(), |dest| {
            dest.write_copy_of_slice(right);
        })
    };
    value.ref_word().raw_word()
}

/// `:erlang.binary_part/3` once the part is known to lie inside the binary:
/// the `size` bytes that start at byte `from`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_binary_part(process: *mut Process, binary_ref: u64, from: i64, size: i64) -> u64 {
    let from = u64::try_from(from).expect("from is checked by :erlang.binary_part/3");
    let size = u64::try_from(size).expect("size is checked by :erlang.binary_part/3");
    unsafe { (&mut *process).slice(binary_ref, from * 8, size * 8) }
        .ref_word()
        .raw_word()
}

/// `:binary.copy/2`: `count` repetitions of the binary, written straight into
/// the one buffer the result lives in. The caller has checked `count >= 0`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_binary_copy(process: *mut Process, subject_ref: u64, count: i64) -> u64 {
    let subject = unsafe { Bin::of_binary(subject_ref) }.bytes();
    let len = subject.len();
    let count = usize::try_from(count).expect("count is checked by :binary.copy/2");
    let total = len.checked_mul(count).expect("a copy's size fits in memory");
    let value = (unsafe { &mut *process }).alloc_bitstring_with(total, (total * 8) as u64, |dest| {
        if len > 0 {
            for repetition in dest.chunks_exact_mut(len) {
                repetition.write_copy_of_slice(subject);
            }
        }
    });
    value.ref_word().raw_word()
}

/// `:binary.referenced_byte_size/1`: the byte count of the buffer the binary
/// references, which is its own size unless it is a view of a larger buffer.
#[unsafe(no_mangle)]
pub extern "C" fn fz_binary_referenced_size(ref_word: u64) -> i64 {
    (unsafe { referenced_byte_len(ref_word) }) as i64
}

/// Single-shot bitstring allocation from module-interned bytes.
///
/// Replaces the begin/write-per-field/finalize sequence for the common
/// case of an all-constant byte-literal bitstring (e.g. `<<1, 2, ..., 70>>`).
/// `ptr` points at a static byte payload baked into the module; the runtime
/// copies through `Heap::alloc_bitstring`, which picks inline / BinView /
/// SharedBin storage by length.
#[unsafe(no_mangle)]
pub extern "C" fn fz_alloc_bitstring_const(process: *mut Process, ptr: u64, byte_len: u64, bit_len: u64) -> u64 {
    // ptr is the address of a module-baked byte payload (Cranelift Local data
    // symbol). It outlives the call; we materialise a slice over it just long
    // enough for Heap::alloc_bitstring to copy / wrap.
    let bytes = unsafe { from_raw_parts(ptr as *const u8, byte_len as usize) };
    let value = (unsafe { &mut *process }).alloc_bitstring(bytes, bit_len);
    value.ref_word().raw_word()
}

/// Allocate a BinRef and a view on the current heap referencing a
/// compiler-baked static SharedBin in `.data`. The static SharedBin's
/// refcount anchor (initial value 1) is kept; we retain to climb to 2,
/// then the new BinRef's lifetime release brings it back to 1 (anchor
/// preserved). The noop destructor never runs in practice.
///
/// `static_sharedbin` is the address of the 48-byte SharedBin struct
/// emitted into `.data` by codegen, with bytes_ptr and destructor
/// relocations resolved by the linker. `bit_len` is the literal's length in
/// bits: the buffer holds whole bytes, and the view says how many bits count.
#[unsafe(no_mangle)]
pub extern "C" fn fz_alloc_binview_from_static(process: *mut Process, static_sharedbin: u64, bit_len: u64) -> u64 {
    let sb = static_sharedbin as *mut SharedBin;
    let handle = unsafe { SharedBinHandle::retain_from_raw(sb) };
    let pb = alloc_buffer_view(
        &mut (unsafe { &mut *process }).heap,
        handle,
        bit_len,
        StubSite::StaticLiteral,
    );
    heap_ref_word(ValueKind::BINVIEW, pb.as_raw() as *const u8)
}

const BS_FIELD_TY_SHIFT: u32 = 0;
const BS_FIELD_SIZE_PRESENT_SHIFT: u32 = 3;
const BS_FIELD_UNIT_SHIFT: u32 = 4;
const BS_FIELD_ENDIAN_SHIFT: u32 = 20;
const BS_FIELD_SIGNED_SHIFT: u32 = 22;
const BS_FIELD_LAST_SHIFT: u32 = 23;
const BS_FIELD_TY_MASK: u64 = 0x7;
const BS_FIELD_UNIT_MASK: u64 = 0xffff;
const BS_FIELD_ENDIAN_MASK: u64 = 0x3;

pub const fn fz_bs_field_spec(
    ty_tag: u32,
    size_present: u32,
    unit: u32,
    endian_tag: u32,
    signed: u32,
    is_last: u32,
) -> u64 {
    ((ty_tag as u64 & BS_FIELD_TY_MASK) << BS_FIELD_TY_SHIFT)
        | (((size_present != 0) as u64) << BS_FIELD_SIZE_PRESENT_SHIFT)
        | ((unit as u64 & BS_FIELD_UNIT_MASK) << BS_FIELD_UNIT_SHIFT)
        | ((endian_tag as u64 & BS_FIELD_ENDIAN_MASK) << BS_FIELD_ENDIAN_SHIFT)
        | (((signed != 0) as u64) << BS_FIELD_SIGNED_SHIFT)
        | (((is_last != 0) as u64) << BS_FIELD_LAST_SHIFT)
}

pub(crate) fn decode_bs_field_spec(spec: u64) -> (u32, u32, u32, u32, u32, u32) {
    (
        ((spec >> BS_FIELD_TY_SHIFT) & BS_FIELD_TY_MASK) as u32,
        ((spec >> BS_FIELD_SIZE_PRESENT_SHIFT) & 1) as u32,
        ((spec >> BS_FIELD_UNIT_SHIFT) & BS_FIELD_UNIT_MASK) as u32,
        ((spec >> BS_FIELD_ENDIAN_SHIFT) & BS_FIELD_ENDIAN_MASK) as u32,
        ((spec >> BS_FIELD_SIGNED_SHIFT) & 1) as u32,
        ((spec >> BS_FIELD_LAST_SHIFT) & 1) as u32,
    )
}

/// Where a field that starts at bit `pos` of the binary `source_ref` names ends,
/// or `None` when the binary does not hold it. A match carries a position, so
/// this is the whole of "does the next field fit" and "where does the next
/// field start".
pub fn bs_field_end(field_spec: u64, size_value: u32, pos: u64, source_ref: u64) -> Option<u64> {
    let (bytes, bit_len) = bit_source(source_ref);
    field_end(field_spec, size_value, pos, bytes, bit_len)
}

/// `bs_field_end` over the bytes a caller already holds.
///
/// A `binary` or `bits` field without a size is the rest of the binary, and only
/// the last field may be one. A `binary` rest holds whole bytes, so a rest that
/// ends between bytes is not one. An integer is at most 64 bits wide. A `utf8` field
/// is one scalar value, 8 to 32 bits wide as the bytes say, and a binary that
/// does not begin with a valid encoding at `pos` does not hold it.
fn field_end(field_spec: u64, size_value: u32, pos: u64, bytes: &[u8], bit_len: u64) -> Option<u64> {
    let width = field_width(field_spec, size_value, pos, bytes, bit_len)?;
    (pos + width <= bit_len).then_some(pos + width)
}

/// How many bits the field that starts at bit `pos` spans, whether or not the
/// binary holds them: `None` for a field that has no width (an unsized
/// `binary` that is not last or ends between bytes, an integer or float of an
/// unsupported width, a `utf8` field that does not begin with a valid
/// encoding).
fn field_width(field_spec: u64, size_value: u32, pos: u64, bytes: &[u8], bit_len: u64) -> Option<u64> {
    let (ty_tag, size_present, unit, _, _, is_last) = decode_bs_field_spec(field_spec);
    let size = (size_present != 0).then_some(size_value as u64);
    let unit = unit as u64;
    match (BitType::from_tag(ty_tag), size) {
        (BitType::Integer, size) => Some(size.unwrap_or(8) * unit).filter(|total| *total <= 64),
        (BitType::Float, size) => Some(size.unwrap_or(64) * unit).filter(|total| *total == 32 || *total == 64),
        (BitType::Binary | BitType::Bits, Some(size)) => Some(size * unit),
        (BitType::Binary, None) => (is_last != 0)
            .then(|| bit_len - pos)
            .filter(|rest| rest.is_multiple_of(8)),
        (BitType::Bits, None) => (is_last != 0).then(|| bit_len - pos),
        (BitType::Utf8, _) => utf8_scalar_at(bytes, pos, bit_len).map(|(_, bits)| bits),
        (ty @ (BitType::Utf16 | BitType::Utf32), _) => unsupported_bit_read(ty),
    }
}

/// `bs_field_end` for generated code that carries no inline arithmetic: the end
/// position, or -1 when the binary does not hold the field.
#[unsafe(no_mangle)]
pub extern "C" fn fz_bs_field_end(field_spec: u64, size_value: u32, pos: u64, source_ref: u64) -> i64 {
    bs_field_end(field_spec, size_value, pos, source_ref).map_or(-1, |end| end as i64)
}

fn unsupported_bit_read(ty: BitType) -> ! {
    panic!("a bitstring match on {ty:?} is not supported by the runtime")
}

/// The scalar value of the UTF-8 sequence at bit `pos`, and the bits it spans.
/// `None` when no valid sequence begins there: the bytes are empty, truncated,
/// or encode a surrogate, an overlong form or a value past U+10FFFF.
fn utf8_scalar_at(bytes: &[u8], pos: u64, bit_len: u64) -> Option<(u32, u64)> {
    let mut window = [0u8; 4];
    let held = utf8_window(bytes, pos, bit_len, &mut window);
    let width = utf8_prefix(&window[..held]).ok().filter(|width| *width > 0)?;
    let scalar = core::str::from_utf8(&window[..width]).ok()?.chars().next()?;
    Some((scalar as u32, width as u64 * 8))
}

/// Fill `window` with the whole bytes that start at bit `pos`, as many as the
/// binary holds up to the window's length, and say how many that is. A match
/// may begin between byte boundaries.
fn utf8_window(bytes: &[u8], pos: u64, bit_len: u64, window: &mut [u8; 4]) -> usize {
    if pos.is_multiple_of(8) {
        let from = (pos / 8) as usize;
        let to = ((bit_len / 8) as usize).min(from + window.len());
        let held = to.saturating_sub(from);
        window[..held].copy_from_slice(&bytes[from..from + held]);
        return held;
    }
    let mut reader = BitReader {
        bytes,
        bit_len: bit_len as usize,
        pos: pos as usize,
    };
    let mut held = 0;
    while held < window.len() {
        let Some(byte) = reader.read_bits(8) else { break };
        window[held] = byte as u8;
        held += 1;
    }
    held
}

/// The bytes of the binary a match reads, and its bit length.
fn bit_source<'a>(source_ref: u64) -> (&'a [u8], u64) {
    let source = unsafe { Bin::of_binary(source_ref) };
    let bit_len = source.bit_len();
    let bytes = unsafe { from_raw_parts(source.ptr(), (bit_len as usize).div_ceil(8)) };
    (bytes, bit_len)
}

/// Read the integer field at bit `pos`: an `integer` field's bits, or the scalar
/// value of a `utf8` field. The caller has proved the field fits
/// (`bs_field_end` answers `Some`), so there is no miss to report.
#[unsafe(no_mangle)]
pub extern "C" fn fz_bs_read_int_ref(source_ref: u64, pos: u64, field_spec: u64, size_value: u32) -> i64 {
    let (ty_tag, _, _, endian_tag, signed, _) = decode_bs_field_spec(field_spec);
    let (bytes, bit_len) = bit_source(source_ref);
    if BitType::from_tag(ty_tag) == BitType::Utf8 {
        let (scalar, _) = utf8_scalar_at(bytes, pos, bit_len)
            .unwrap_or_else(|| panic!("fz_bs_read_int_ref: the utf8 field at bit {pos} does not fit"));
        return i64::from(scalar);
    }
    let end = field_end(field_spec, size_value, pos, bytes, bit_len)
        .unwrap_or_else(|| panic!("fz_bs_read_int_ref: the field at bit {pos} does not fit"));
    let total = (end - pos) as u32;
    let mut reader = BitReader {
        bytes,
        bit_len: bit_len as usize,
        pos: pos as usize,
    };
    let raw = reader.read_bits(total as usize).expect("a field that fits is readable");
    let raw = apply_endian_for_read(raw, total, Endian::from_tag(endian_tag));
    if signed != 0 {
        sign_extend(raw, total)
    } else {
        raw as i64
    }
}

/// Read the `binary` or `bits` field at bit `pos` as a binary: the source
/// itself when the field is all of it, and a new binary otherwise. The caller
/// has proved the field fits (`bs_field_end` answers `Some`); a debug build
/// checks the claim.
#[unsafe(no_mangle)]
pub extern "C" fn fz_bs_read_binary_ref(
    process: *mut Process,
    source_ref: u64,
    pos: u64,
    field_spec: u64,
    size_value: u32,
) -> u64 {
    let (ty_tag, ..) = decode_bs_field_spec(field_spec);
    match BitType::from_tag(ty_tag) {
        BitType::Binary | BitType::Bits => {}
        BitType::Float => panic!("a float field cannot be materialized as a one-word value"),
        BitType::Utf8 => panic!("a utf8 field is read as an integer"),
        ty => unsupported_bit_read(ty),
    }
    let (bytes, bit_len) = bit_source(source_ref);
    let width = field_width(field_spec, size_value, pos, bytes, bit_len)
        .unwrap_or_else(|| panic!("fz_bs_read_binary_ref: the field at bit {pos} has no width"));
    debug_assert!(
        pos + width <= bit_len,
        "fz_bs_read_binary_ref: the field at bit {pos} of {width} bits runs past the {bit_len} bits it reads"
    );
    fz_bs_slice_ref(process, source_ref, pos, width)
}

/// The `bit_len` bits of the binary `source_ref` from bit `pos`, as a binary:
/// what `Heap::slice` makes. The caller has proved the window lies inside
/// the source, so nothing is checked here.
#[unsafe(no_mangle)]
pub extern "C" fn fz_bs_slice_ref(process: *mut Process, source_ref: u64, pos: u64, bit_len: u64) -> u64 {
    let process = unsafe { &mut *process };
    unsafe { process.slice(source_ref, pos, bit_len) }.ref_word().raw_word()
}

// ===== Map cluster =====
//
// Maps publish one sorted sequence with unique strict structural keys.
// Construction freezes once; immutable updates preserve the same order.

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_empty(process: *mut Process) -> u64 {
    map_ref_word_from_bits((unsafe { &mut *process }).heap.alloc_map_slots(&[]))
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_dest_begin(process: *mut Process, extra: u32) -> u64 {
    map_ref_word_from_bits((unsafe { &mut *process }).heap.alloc_map_destination(extra as usize))
}

/// A destination for `%{base | k: v, ...}`: `base`'s entries, which the puts
/// replace. A struct's destination is a copy of the struct.
#[unsafe(no_mangle)]
pub extern "C" fn fz_map_dest_begin_update(process: *mut Process, base_ref_word: u64) -> u64 {
    let base = any_value_ref_from_word(base_ref_word, "fz_map_dest_begin_update base");
    destination_ref_word((unsafe { &mut *process }).heap.alloc_map_update(base))
}

/// Store one entry and answer the destination to continue with: the null
/// reference once an update has named a key its base lacks. The key and the
/// value each arrive as their stored word and kind.
#[unsafe(no_mangle)]
pub extern "C" fn fz_map_dest_put(
    process: *mut Process,
    dest_ref_word: u64,
    key_word: u64,
    key_kind: u64,
    value_word: u64,
    value_kind: u64,
) -> u64 {
    let dest_bits = destination_bits_from_ref_word(dest_ref_word, "fz_map_dest_put dest");
    let key = Stored {
        word: key_word,
        kind: key_kind,
    }
    .value("fz_map_dest_put key");
    let value = Stored {
        word: value_word,
        kind: value_kind,
    }
    .value("fz_map_dest_put value");
    destination_ref_word(unsafe { (*process).heap.map_destination_put(dest_bits, key, value) })
}

/// The published map, or the null reference when an update named a key its
/// base lacks; the caller tests for it and raises `KeyError`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_map_dest_freeze(process: *mut Process, dest_ref_word: u64) -> u64 {
    let dest_bits = destination_bits_from_ref_word(dest_ref_word, "fz_map_dest_freeze dest");
    (unsafe { &mut *process })
        .heap
        .map_destination_freeze(dest_bits)
        .unwrap_or_else(AnyValueRef::null)
        .raw_word()
}

/// Publish a map literal's destination whose entries compiled code put in
/// key order with no key repeated.
#[unsafe(no_mangle)]
pub extern "C" fn fz_map_dest_publish(process: *mut Process, dest_ref_word: u64) -> u64 {
    let dest_bits = destination_bits_from_ref_word(dest_ref_word, "fz_map_dest_publish dest");
    (unsafe { &mut *process })
        .heap
        .map_destination_publish(dest_bits)
        .raw_word()
}

/// `Map.get/2`: the value `map` binds to the key, given as its stored word
/// and kind, or `nil`. A resource answers `nil` for every key.
#[unsafe(no_mangle)]
pub extern "C" fn fz_map_get_ref(process: *mut Process, map_ref_word: u64, key_word: u64, key_kind: u64) -> u64 {
    let map = any_value_ref_from_word(map_ref_word, "fz_map_get_ref map");
    map_get(
        process,
        map,
        Stored {
            word: key_word,
            kind: key_kind,
        }
        .value("fz_map_get_ref key"),
    )
}

#[inline(always)]
fn map_get(process: *mut Process, map: AnyValueRef, key: AnyValue) -> u64 {
    if map.tag() == ValueKind::RESOURCE {
        return nil_atom_ref().raw_word();
    }
    (unsafe { &mut *process })
        .heap
        .read_map_value(map, key)
        .unwrap_or_else(nil_atom_ref)
        .raw_word()
}

fn resource_payload_ref(resource: AnyValueRef) -> AnyValueRef {
    let stub = unsafe { ResourceStub::from_raw(resource.resource_addr().expect("resource payload")) };
    AnyValueRef::from_scalar_slot(ValueKind::INT, stub.payload_slot()).expect("resource integer payload ref")
}

fn nil_atom_ref() -> AnyValueRef {
    AnyValueRef::atom(NIL_ATOM_ID)
}

/// `Map.delete/2`: the map without `key`, or the same map when absent.
#[unsafe(no_mangle)]
pub extern "C" fn fz_map_delete(process: *mut Process, map_ref: u64, key_word: u64, key_kind: u64) -> u64 {
    let map = any_value_ref_from_word(map_ref, "fz_map_delete map");
    let key = Stored {
        word: key_word,
        kind: key_kind,
    }
    .value("fz_map_delete key");
    (unsafe { &mut *process }).heap.map_view_delete(map, key).raw_word()
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_count(process: *mut Process, map_ref_word: u64) -> i64 {
    let map = any_value_ref_from_word(map_ref_word, "fz_map_count map");
    let heap = &(unsafe { &*process }).heap;
    heap.map_view_count(heap.expect_map_layout(map, "fz_map_count")) as i64
}

/// The number of entries of a map or struct; -1 for any other value, so the
/// question "does this value have `n` entries" is total over what it is handed.
#[unsafe(no_mangle)]
pub extern "C" fn fz_map_size_of(process: *mut Process, value_ref_word: u64) -> i64 {
    let value = any_value_ref_from_word(value_ref_word, "fz_map_size_of value");
    let heap = &(unsafe { &*process }).heap;
    heap.map_layout(value)
        .map_or(-1, |layout| heap.map_view_count(layout) as i64)
}

/// Whether `map`, in either layout, holds `key`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_map_has_key(process: *mut Process, map_ref_word: u64, key_word: u64, key_kind: u64) -> u64 {
    let map = any_value_ref_from_word(map_ref_word, "fz_map_has_key map");
    let key = Stored {
        word: key_word,
        kind: key_kind,
    }
    .value("fz_map_has_key key");
    let heap = &(unsafe { &*process }).heap;
    u64::from(heap.map_view_has_key(heap.expect_map_layout(map, "fz_map_has_key"), key))
}

/// The arity of a tuple, or `None` for any other value. Structs share the
/// STRUCT tag with tuples, and only a tuple schema carries an arity.
fn tuple_arity_of(process: *mut Process, value: AnyValueRef) -> Option<usize> {
    let addr = value.struct_addr().ok()?;
    let schema_id = unsafe { struct_schema_id(addr as *const u8) };
    let registry = (unsafe { &*process }).heap.schemas_registry();
    match registry.borrow().get(schema_id).identity {
        crate::heap::SchemaIdentity::Tuple(arity) => Some(arity),
        _ => None,
    }
}

/// The number of arguments a function takes. Its captures are not arguments.
#[unsafe(no_mangle)]
pub extern "C" fn fz_function_arity(_process: *mut Process, function_ref_word: u64) -> i64 {
    let addr = closure_addr_from_tagged(function_ref_word).expect("fz_function_arity: a function");
    i64::from(unsafe { closure_arity(addr) })
}

/// What `&Mod.fun/arity` spells for a function: the list `[module, name,
/// arity]`, the first two as atoms, when the function is a named one in a
/// module, and `[]` for a lambda or a function outside every module.
#[unsafe(no_mangle)]
pub extern "C" fn fz_function_name(process: *mut Process, function_ref_word: u64) -> u64 {
    let addr = closure_addr_from_tagged(function_ref_word).expect("fz_function_name: a function");
    let process = unsafe { &mut *process };
    let Some((module, name)) = process
        .node
        .closure_module_and_name(unsafe { closure_denotation(addr) })
    else {
        return AnyValueRef::empty_list().raw_word();
    };
    let arity = i64::from(unsafe { closure_arity(addr) });
    let (module, name) = (process.node.intern_atom(&module), process.node.intern_atom(&name));
    let heap = &mut process.heap;
    let list = heap
        .alloc_list_cons_int(arity, AnyValueRef::empty_list())
        .expect("fz_function_name arity");
    let list = heap.alloc_list_cons_atom(name, list).expect("fz_function_name name");
    heap.alloc_list_cons_atom(module, list)
        .expect("fz_function_name module")
        .raw_word()
}

/// The number of fields of a tuple; -1 for any other value, so a caller checks
/// the answer instead of aborting.
#[unsafe(no_mangle)]
pub extern "C" fn fz_tuple_size(process: *mut Process, tuple_ref_word: u64) -> i64 {
    let value = any_value_ref_from_word(tuple_ref_word, "fz_tuple_size tuple");
    tuple_arity_of(process, value).map_or(-1, |arity| arity as i64)
}

/// The field of a tuple at a zero-based index; `nil` where the value is no
/// tuple or the index is outside it, so the call is total over what it is
/// handed. Callers inside the domain never see the `nil`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_tuple_elem(process: *mut Process, tuple_ref_word: u64, index: i64) -> u64 {
    let value = any_value_ref_from_word(tuple_ref_word, "fz_tuple_elem tuple");
    let in_domain = tuple_arity_of(process, value).is_some_and(|arity| usize::try_from(index).is_ok_and(|i| i < arity));
    if !in_domain {
        return nil_atom_ref().raw_word();
    }
    (unsafe { &*process })
        .heap
        .read_struct_field_ref(value, (index as u32) * 8)
        .expect("fz_tuple_elem field")
        .raw_word()
}

/// A copy of a tuple with the field at a zero-based index replaced by a
/// value; `nil` where the first argument is no tuple or the index is outside
/// it, so the call is total over what it is handed. The original is never
/// written. Callers inside the domain never see the `nil`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_tuple_put(process: *mut Process, tuple_ref_word: u64, index: i64, value_ref_word: u64) -> u64 {
    let tuple = any_value_ref_from_word(tuple_ref_word, "fz_tuple_put tuple");
    let value = any_value_ref_from_word(value_ref_word, "fz_tuple_put value");
    let Some(arity) = tuple_arity_of(process, tuple) else {
        return nil_atom_ref().raw_word();
    };
    let Some(index) = usize::try_from(index).ok().filter(|&index| index < arity) else {
        return nil_atom_ref().raw_word();
    };
    let layout = SlotLayout::of(arity);
    let copy_word = copy_struct_counted(process, tuple_ref_word, arity as u32, RuntimeReuseSite::TupleCopy);
    let stored = Stored::of(AnyValue::from_ref(value).expect("fz_tuple_put value"));
    fz_struct_store_ref(
        process,
        copy_word,
        SlotLayout::slot_offset(index) as u32,
        layout.kind_offset(index) as u32,
        stored.word,
        stored.kind,
    );
    copy_word
}

/// A tuple whose fields are the `arity` elements of a proper list, in order.
/// The arity is known only at run time, so the tuple's schema is registered on
/// demand: the registry hands back the existing one when compiled code already
/// uses that arity.
#[unsafe(no_mangle)]
pub extern "C" fn fz_list_to_tuple(process: *mut Process, list_ref_word: u64, arity: i64) -> u64 {
    let arity = usize::try_from(arity).expect("fz_list_to_tuple arity");
    let process = unsafe { &mut *process };
    let schema_id = process.heap.schemas_registry().borrow_mut().tuple(arity);
    let object = process.heap.alloc_struct(schema_id);
    let layout = SlotLayout::of(arity);
    let mut cursor = any_value_ref_from_word(list_ref_word, "fz_list_to_tuple list");
    for index in 0..arity {
        let element = AnyValue::from_ref(list_head_ref(cursor).expect("fz_list_to_tuple head"))
            .expect("fz_list_to_tuple element");
        unsafe {
            process
                .heap
                .store_struct_field(
                    object,
                    SlotLayout::slot_offset(index),
                    layout.kind_offset(index),
                    element,
                )
                .expect("fz_list_to_tuple store");
        }
        cursor = list_tail_ref(cursor).expect("fz_list_to_tuple tail");
    }
    heap_ref_word(ValueKind::STRUCT, object)
}

/// The length of a proper list; -1 where the chain ends in anything but the
/// empty list, so an improper list or a non-list is told apart from `[]`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_list_length(list_ref_word: u64) -> i64 {
    let mut cursor = any_value_ref_from_word(list_ref_word, "fz_list_length list");
    let mut length = 0i64;
    while cursor.tag() == ValueKind::LIST && !cursor.is_empty_list() {
        length += 1;
        cursor = list_tail_ref(cursor).expect("fz_list_length tail");
    }
    if cursor.is_empty_list() { length } else { -1 }
}

/// `Map.to_list/1`: the map's `{key, value}` pairs, in the map's own order.
#[unsafe(no_mangle)]
pub extern "C" fn fz_map_to_list(process: *mut Process, map_ref_word: u64) -> u64 {
    map_list(process, map_ref_word, MapPart::Pairs, "fz_map_to_list")
}

/// `Map.keys/1`: the map's keys, in the map's own order.
#[unsafe(no_mangle)]
pub extern "C" fn fz_map_keys(process: *mut Process, map_ref_word: u64) -> u64 {
    map_list(process, map_ref_word, MapPart::Keys, "fz_map_keys")
}

/// `Map.values/1`: the map's values, in the map's own order.
#[unsafe(no_mangle)]
pub extern "C" fn fz_map_values(process: *mut Process, map_ref_word: u64) -> u64 {
    map_list(process, map_ref_word, MapPart::Values, "fz_map_values")
}

fn map_list(process: *mut Process, map_ref_word: u64, part: MapPart, context: &str) -> u64 {
    let map = any_value_ref_from_word(map_ref_word, context);
    (unsafe { &mut *process }).heap.map_list(map, part).raw_word()
}

fn map_put_slot_value(process: *mut Process, map_ref_word: u64, key: AnyValue, value: AnyValue) -> u64 {
    let map = any_value_ref_from_word(map_ref_word, "map_put map");
    (unsafe { &mut *process }).heap.map_put_slot(map, key, value).raw_word()
}

/// `map` with `key` bound to `value`, each given as its stored word and kind.
#[unsafe(no_mangle)]
pub extern "C" fn fz_map_put(
    process: *mut Process,
    map_ref_word: u64,
    key_word: u64,
    key_kind: u64,
    value_word: u64,
    value_kind: u64,
) -> u64 {
    map_put_slot_value(
        process,
        map_ref_word,
        Stored {
            word: key_word,
            kind: key_kind,
        }
        .value("fz_map_put key"),
        Stored {
            word: value_word,
            kind: value_kind,
        }
        .value("fz_map_put value"),
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_from_kv(process: *mut Process, keys_ref_word: u64, values_ref_word: u64) -> u64 {
    let mut keys = any_value_ref_from_word(keys_ref_word, "fz_map_from_kv keys");
    let mut values = any_value_ref_from_word(values_ref_word, "fz_map_from_kv values");
    let mut entries: Vec<(AnyValueRef, AnyValueRef)> = Vec::new();
    while !keys.is_empty_list() {
        let key = list_head_ref(keys).expect("fz_map_from_kv key");
        let value = list_head_ref(values).expect("fz_map_from_kv value");
        entries.push((key, value));
        keys = list_tail_ref(keys).expect("fz_map_from_kv keys tail");
        values = list_tail_ref(values).expect("fz_map_from_kv values tail");
    }
    map_ref_word_from_bits((unsafe { &mut *process }).heap.alloc_map_refs_bits(&entries))
}

/// `Map.put` with an ATOM value, taking the atom as a tagged ref.
///
/// An `atom` parameter of an fz extern marshals as a tagged ref, so the id is
/// loaded from the ref here.
#[unsafe(no_mangle)]
pub extern "C" fn fz_map_is_map(process: *mut Process, map_ref_word: u64) -> u8 {
    let value = any_value_ref_from_word(map_ref_word, "fz_map_is_map");
    unsafe { &*process }.heap.map_layout(value).is_some() as u8
}

// ===== Alloc cluster =====

/// `System.argv/0`: the program's command line, as a list of binaries holding
/// each argument's exact bytes, read from the driver's execution context.
#[unsafe(no_mangle)]
pub extern "C" fn fz_system_argv(process: *mut Process) -> u64 {
    let ctx = unsafe { process_ctx(process) };
    let process = unsafe { &mut *process };
    let mut list = AnyValueRef::empty_list();
    for arg in ctx.argv().iter().rev() {
        let binary = process.alloc_bitstring(arg, (arg.len() * 8) as u64);
        list = process
            .heap
            .alloc_list_cons_ref(binary.ref_word(), list)
            .expect("fz_system_argv");
    }
    list.raw_word()
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_list_is_cons(list_ref_word: u64) -> u64 {
    let list = any_value_ref_from_word(list_ref_word, "fz_list_is_cons");
    u64::from(list.tag() == ValueKind::LIST && !list.is_empty_list())
}

/// A cell holding `head` in front of the tail given as its stored word and
/// kind. A list tail is linked; any other value, whatever its kind, ends the
/// list in a terminator cell, and nothing is boxed to carry it.
fn list_cons(process: *mut Process, head: AnyValue, tail_word: u64, tail_kind: u64, context: &str) -> u64 {
    let tail = Stored {
        word: tail_word,
        kind: tail_kind,
    }
    .value(context);
    (unsafe { &mut *process })
        .heap
        .alloc_list_cons_any(head, tail)
        .raw_word()
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_list_cons_any(process: *mut Process, head_ref_word: u64, tail_word: u64, tail_kind: u64) -> u64 {
    let head = any_value_from_ref_word(head_ref_word, "fz_list_cons_any head");
    list_cons(process, head, tail_word, tail_kind, "fz_list_cons_any tail")
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_list_cons_int(process: *mut Process, head: i64, tail_word: u64, tail_kind: u64) -> u64 {
    list_cons(
        process,
        AnyValue::int(head),
        tail_word,
        tail_kind,
        "fz_list_cons_int tail",
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_list_cons_float(process: *mut Process, head: f64, tail_word: u64, tail_kind: u64) -> u64 {
    list_cons(
        process,
        AnyValue::float(head),
        tail_word,
        tail_kind,
        "fz_list_cons_float tail",
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_list_cons_atom(process: *mut Process, atom_id: u64, tail_word: u64, tail_kind: u64) -> u64 {
    list_cons(
        process,
        AnyValue::atom(atom_id as u32),
        tail_word,
        tail_kind,
        "fz_list_cons_atom tail",
    )
}

// Reading a list head/tail is a pure dereference of the self-describing list
// pointer — no allocation, no heap state — so these take no process.
#[unsafe(no_mangle)]
pub extern "C" fn fz_list_head_ref(list_ref_word: u64) -> u64 {
    let list = any_value_ref_from_word(list_ref_word, "fz_list_head_ref");
    list_head_ref(list).expect("fz_list_head_ref").raw_word()
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_list_head_int_ref(list_ref_word: u64) -> i64 {
    let head = fz_list_head_ref(list_ref_word);
    fz_ref_load_int(head)
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_list_head_float_ref(list_ref_word: u64) -> f64 {
    let head = fz_list_head_ref(list_ref_word);
    fz_ref_load_float(head)
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_list_tail_ref(list_ref_word: u64) -> u64 {
    let list = any_value_ref_from_word(list_ref_word, "fz_list_tail_ref");
    list_tail_ref(list).expect("fz_list_tail_ref").raw_word()
}

/// Mark the spine of the list whose first cell is at `cell_addr` shared, up
/// to the first cell already marked. Generated code calls it only for a first
/// cell it has seen unmarked.
#[unsafe(no_mangle)]
pub extern "C" fn fz_share_list_spine(cell_addr: *mut u8) {
    unsafe { ListCons::share_spine(cell_addr) };
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_mark_published_ref_aliased(process: *mut Process, value_ref_word: u64) -> u64 {
    let value = any_value_ref_from_word(value_ref_word, "fz_mark_published_ref_aliased");
    (unsafe { &mut *process })
        .heap
        .mark_published_ref_aliased(value)
        .expect("fz_mark_published_ref_aliased")
        .raw_word()
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_list_reuse_or_cons_parts(
    process: *mut Process,
    list_ref_word: u64,
    head_raw: u64,
    head_kind_tag: u64,
    tail_word: u64,
    tail_kind: u64,
    may_rewrite: u64,
) -> u64 {
    let list = any_value_ref_from_word(list_ref_word, "fz_list_reuse_or_cons_parts list");
    let head_kind = ValueKind::new(head_kind_tag as u8).expect("fz_list_reuse_or_cons_parts head kind");
    let tail = Stored {
        word: tail_word,
        kind: tail_kind,
    }
    .value("fz_list_reuse_or_cons_parts tail");
    let process = unsafe { &mut *process };
    let result = process
        .heap
        .reuse_or_alloc_list_cons_raw_kind(list, head_raw, head_kind, tail, may_rewrite != 0)
        .expect("fz_list_reuse_or_cons_parts");
    if result == list {
        process.node.runtime_reuses.hit(RuntimeReuseSite::ListReuse);
    } else {
        process.node.runtime_reuses.miss(RuntimeReuseSite::ListReuse);
    }
    result.raw_word()
}

/// An unpublished copy of a struct of `fields` fields, for an update that
/// may not rewrite its base. Compiled code stores the fields the update
/// replaces next, in place, before anything can read it.
#[unsafe(no_mangle)]
pub extern "C" fn fz_struct_copy(process: *mut Process, struct_ref_word: u64, fields: u32) -> u64 {
    copy_struct_counted(process, struct_ref_word, fields, RuntimeReuseSite::StructCopy)
}

/// The copy `site` is the miss of.
fn copy_struct_counted(process: *mut Process, struct_ref_word: u64, fields: u32, site: RuntimeReuseSite) -> u64 {
    let object = any_value_ref_from_word(struct_ref_word, "fz_struct_copy")
        .struct_addr()
        .expect("fz_struct_copy");
    let process = unsafe { &mut *process };
    process.node.runtime_reuses.miss(site);
    let copy = unsafe {
        process
            .heap
            .copy_struct(object.cast_const(), SlotLayout::of(fields as usize))
    };
    heap_ref_word(ValueKind::STRUCT, copy)
}

/// The struct an update of a struct of `fields` fields stores into: the base
/// itself when `may_rewrite` is set and the base is not shared, otherwise
/// `fz_struct_copy`'s copy. The answer is the base exactly when it is
/// rewritten. Compiled native code makes the same decision inline.
#[unsafe(no_mangle)]
pub extern "C" fn fz_struct_reuse_or_copy(
    process: *mut Process,
    struct_ref_word: u64,
    fields: u32,
    may_rewrite: u64,
) -> u64 {
    let object = any_value_ref_from_word(struct_ref_word, "fz_struct_reuse_or_copy")
        .struct_addr()
        .expect("fz_struct_reuse_or_copy");
    if may_rewrite == 0 || unsafe { struct_is_shared(object) } {
        return copy_struct_counted(process, struct_ref_word, fields, RuntimeReuseSite::StructReuse);
    }
    let process = unsafe { &mut *process };
    // A collection shares every struct it keeps, so an unshared one is young.
    process.heap.assert_written_object_is_young(object);
    process.node.runtime_reuses.hit(RuntimeReuseSite::StructReuse);
    struct_ref_word
}

/// Store a value held as a reference into a struct under construction, at
/// its field's raw and kind offsets. Compiled code stores a value whose kind
/// it knows in place; this is the store for one it does not, or for a list,
/// which the store shares.
#[unsafe(no_mangle)]
pub extern "C" fn fz_struct_store_ref(
    process: *mut Process,
    struct_ref_word: u64,
    slot_offset: u32,
    kind_offset: u32,
    value_word: u64,
    value_kind: u64,
) {
    let object = any_value_ref_from_word(struct_ref_word, "fz_struct_store_ref object")
        .struct_addr()
        .expect("fz_struct_store_ref object");
    let value = Stored {
        word: value_word,
        kind: value_kind,
    }
    .value("fz_struct_store_ref value");
    unsafe {
        (&mut *process)
            .heap
            .store_struct_field(object, slot_offset as usize, kind_offset as usize, value)
    }
    .expect("fz_struct_store_ref");
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_struct_get_field_ref(process: *mut Process, struct_ref_word: u64, field_offset: u32) -> u64 {
    let value = any_value_ref_from_word(struct_ref_word, "fz_struct_get_field_ref");
    (unsafe { &mut *process })
        .heap
        .read_struct_field_ref(value, field_offset)
        .expect("fz_struct_get_field_ref")
        .raw_word()
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_struct_get_named_field_ref(process: *mut Process, value_ref_word: u64, field_atom_id: u64) -> u64 {
    let value_ref = any_value_ref_from_word(value_ref_word, "fz_struct_get_named_field_ref");
    if value_ref.tag() == ValueKind::RESOURCE {
        let field_name = (unsafe { &*process }).node.atom_name(field_atom_id as u32);
        assert_eq!(field_name.as_deref(), Some("value"), "a resource's one field is value");
        return resource_payload_ref(value_ref).raw_word();
    }
    map_get(process, value_ref, AnyValue::atom(field_atom_id as u32))
}

/// The module a struct value belongs to, as a value ref: its `__struct__`
/// key, read the same way in either map layout.
#[unsafe(no_mangle)]
pub extern "C" fn fz_struct_module(process: *mut Process, value_ref_word: u64) -> u64 {
    let key = unsafe { &*process }.node.intern_atom(STRUCT_MODULE_FIELD);
    let value = any_value_ref_from_word(value_ref_word, "fz_struct_module");
    map_get(process, value, AnyValue::atom(key))
}

/// The struct schema of the module a map names, as a `NamedSchema` word.
#[unsafe(no_mangle)]
pub extern "C" fn fz_map_named_schema_ref(process: *mut Process, map_ref_word: u64) -> u32 {
    let map = any_value_ref_from_word(map_ref_word, "fz_map_named_schema_ref");
    unsafe { &*process }.heap.named_schema(map).word()
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_closure_get_capture_ref(closure_ref_word: u64, index: u64) -> u64 {
    let value = AnyValueRef::from_raw_word(closure_ref_word).unwrap_or_else(|err| {
        panic!(
            "fz_closure_get_capture_ref idx={} invalid any value ref {:#x}: {:?}",
            index, closure_ref_word, err
        )
    });
    if value.tag() != ValueKind::CLOSURE {
        panic!(
            "fz_closure_get_capture_ref idx={} expected closure ref, got tag {:?} word={:#x}",
            index,
            value.tag(),
            closure_ref_word
        );
    }
    match closure_capture_ref(value, index as usize) {
        Ok(capture) => capture.raw_word(),
        Err(err) => {
            let addr = value.closure_addr().expect("fz_closure_get_capture_ref closure");
            panic!(
                "fz_closure_get_capture_ref idx={} denotation={:?} captured_count={} code_ptr={:#x}: {:?}",
                index,
                unsafe { closure_denotation(addr) },
                unsafe { closure_captured_count(addr) },
                unsafe { closure_fn_ptr(addr) },
                err
            )
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_closure_set_capture_ref(
    process: *mut Process,
    closure_ref_word: u64,
    index: u64,
    value_word: u64,
    value_kind: u64,
) {
    let closure = any_value_ref_from_word(closure_ref_word, "fz_closure_set_capture_ref closure")
        .closure_addr()
        .expect("fz_closure_set_capture_ref closure");
    let value = Stored {
        word: value_word,
        kind: value_kind,
    }
    .value("fz_closure_set_capture_ref value");
    unsafe {
        (&mut *process)
            .heap
            .write_closure_capture_value(closure, index as usize, value)
    };
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_closure_set_capture_i64(process: *mut Process, closure_ref_word: u64, index: u64, value: i64) {
    let closure = any_value_ref_from_word(closure_ref_word, "fz_closure_set_capture_i64 closure");
    let addr = closure.closure_addr().expect("fz_closure_set_capture_i64 closure");
    unsafe {
        (&mut *process)
            .heap
            .write_closure_capture_value(addr, index as usize, AnyValue::Int(value))
    };
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_closure_set_capture_f64(process: *mut Process, closure_ref_word: u64, index: u64, value: f64) {
    let closure = any_value_ref_from_word(closure_ref_word, "fz_closure_set_capture_f64 closure");
    let addr = closure.closure_addr().expect("fz_closure_set_capture_f64 closure");
    unsafe {
        (&mut *process)
            .heap
            .write_closure_capture_value(addr, index as usize, AnyValue::float(value))
    };
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_closure_set_capture_atom(process: *mut Process, closure_ref_word: u64, index: u64, value: u64) {
    let closure = any_value_ref_from_word(closure_ref_word, "fz_closure_set_capture_atom closure");
    let addr = closure.closure_addr().expect("fz_closure_set_capture_atom closure");
    unsafe {
        (&mut *process)
            .heap
            .write_closure_capture_value(addr, index as usize, AnyValue::Atom(value as u32))
    };
}

// ===== Arith / cmp / eq cluster =====

/// Checked `==` between a dynamic `AnyValueRef` and an unboxed int/atom raw
/// payload, with no allocation on either side. `expected_tag` is an
/// `INT`/`ATOM` `ValueKind` tag byte. Reads `ref_word`'s runtime tag and
/// returns false (not a panic) whenever it doesn't match `expected_tag`, so
/// codegen can call this whenever one side of an `==`/`!=` is natively
/// unboxed (a literal, a monomorphized parameter, a projected pattern tag,
/// etc. — e.g. matching a `:cont`/`:halt` protocol tag, or an `Enum.member?`
/// scan against an int argument) without first proving the other side's
/// static type — the proof `fz_value_eq_ref`'s generic path would otherwise
/// need before it could avoid materializing the unboxed side into a heap
/// scalar box.
#[unsafe(no_mangle)]
pub extern "C" fn fz_value_eq_raw_const(ref_word: u64, expected_tag: u32, raw: u64) -> u64 {
    let value = any_value_ref_from_word(ref_word, "fz_value_eq_raw_const");
    let Some(expected_tag) = ValueKind::new(expected_tag as u8) else {
        return 0;
    };
    u64::from(value.tag() == expected_tag && value.storage_raw() == Ok(raw))
}

/// Widening language term order, borrowed from the same comparator that owns
/// strict map-key identity. Each operand is its stored word and kind. Returns
/// -1, 0, or 1.
#[unsafe(no_mangle)]
pub extern "C" fn fz_value_cmp_ref(process: *mut Process, a_word: u64, a_kind: u64, b_word: u64, b_kind: u64) -> i64 {
    let a = Stored {
        word: a_word,
        kind: a_kind,
    }
    .value("fz_value_cmp_ref lhs");
    let b = Stored {
        word: b_word,
        kind: b_kind,
    }
    .value("fz_value_cmp_ref rhs");
    compare_values(process, a, b, NumericMode::Widening) as i64
}

/// Exact mixed-number comparison of two unboxed lanes; no process or allocation.
#[unsafe(no_mangle)]
pub extern "C" fn fz_int_float_cmp(integer: i64, float: f64) -> i64 {
    crate::term::compare_int_float(integer, float) as i64
}

macro_rules! numeric_bool_export {
    ($name:ident, ($left:ident : $left_ty:ty, $right:ident : $right_ty:ty) => $answer:expr) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn $name($left: $left_ty, $right: $right_ty) -> u64 {
            u64::from($answer)
        }
    };
}

numeric_bool_export!(fz_op_lt_ii, (left: i64, right: i64) => left < right);
numeric_bool_export!(fz_op_lte_ii, (left: i64, right: i64) => left <= right);
numeric_bool_export!(fz_op_gt_ii, (left: i64, right: i64) => left > right);
numeric_bool_export!(fz_op_gte_ii, (left: i64, right: i64) => left >= right);
numeric_bool_export!(fz_op_lt_ff, (left: f64, right: f64) => left < right);
numeric_bool_export!(fz_op_lte_ff, (left: f64, right: f64) => left <= right);
numeric_bool_export!(fz_op_gt_ff, (left: f64, right: f64) => left > right);
numeric_bool_export!(fz_op_gte_ff, (left: f64, right: f64) => left >= right);
numeric_bool_export!(fz_op_lt_if, (left: i64, right: f64) => crate::term::compare_int_float(left, right).is_lt());
numeric_bool_export!(fz_op_lte_if, (left: i64, right: f64) => crate::term::compare_int_float(left, right).is_le());
numeric_bool_export!(fz_op_gt_if, (left: i64, right: f64) => crate::term::compare_int_float(left, right).is_gt());
numeric_bool_export!(fz_op_gte_if, (left: i64, right: f64) => crate::term::compare_int_float(left, right).is_ge());
numeric_bool_export!(fz_op_lt_fi, (left: f64, right: i64) => crate::term::compare_int_float(right, left).is_gt());
numeric_bool_export!(fz_op_lte_fi, (left: f64, right: i64) => crate::term::compare_int_float(right, left).is_ge());
numeric_bool_export!(fz_op_gt_fi, (left: f64, right: i64) => crate::term::compare_int_float(right, left).is_lt());
numeric_bool_export!(fz_op_gte_fi, (left: f64, right: i64) => crate::term::compare_int_float(right, left).is_le());

// Equality and identity differ only on floats, and on exactly the same rule the
// structural comparator uses: `==` widens, so `0.0 == -0.0` is true, while
// `===` is strict, so `0.0 === -0.0` is false. A non-finite float is not a
// language value, so neither rule has a NaN case to answer.
numeric_bool_export!(fz_op_eq_ii, (left: i64, right: i64) => left == right);
numeric_bool_export!(fz_op_eq_ff, (left: f64, right: f64) => left == right);
numeric_bool_export!(fz_op_eq_if, (left: i64, right: f64) => crate::term::compare_int_float(left, right).is_eq());
numeric_bool_export!(fz_op_eq_fi, (left: f64, right: i64) => crate::term::compare_int_float(right, left).is_eq());
numeric_bool_export!(fz_op_neq_ii, (left: i64, right: i64) => left != right);
numeric_bool_export!(fz_op_neq_ff, (left: f64, right: f64) => left != right);
numeric_bool_export!(fz_op_neq_if, (left: i64, right: f64) => crate::term::compare_int_float(left, right).is_ne());
numeric_bool_export!(fz_op_neq_fi, (left: f64, right: i64) => crate::term::compare_int_float(right, left).is_ne());
numeric_bool_export!(fz_op_identical_ii, (left: i64, right: i64) => left == right);
numeric_bool_export!(fz_op_identical_ff, (left: f64, right: f64) => left.total_cmp(&right).is_eq());
numeric_bool_export!(fz_op_not_identical_ii, (left: i64, right: i64) => left != right);
numeric_bool_export!(fz_op_not_identical_ff, (left: f64, right: f64) => left.total_cmp(&right).is_ne());

// Binaries cross the truthful fz ABI as tagged words, never as C byte pointers
// without their lengths. The declared `binary` parameter proves each word names
// a Bitstring or BinView, `Bin::of_binary` decodes it, and the answer is
// `Bin`'s equality or term order, the same order `TermComparator` gives two
// bitstrings. `===` and `!==` of two binaries are `==` and `!=`: no numeric
// widening applies to a binary.
macro_rules! binary_bool_export {
    ($name:ident, |$left:ident, $right:ident| $answer:expr) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn $name(_process: *mut Process, left: u64, right: u64) -> u64 {
            let ($left, $right) = unsafe { (Bin::of_binary(left), Bin::of_binary(right)) };
            u64::from($answer)
        }
    };
}

binary_bool_export!(fz_op_eq_bb, |left, right| left == right);
binary_bool_export!(fz_op_neq_bb, |left, right| left != right);
binary_bool_export!(fz_op_lt_bb, |left, right| left.cmp(&right).is_lt());
binary_bool_export!(fz_op_lte_bb, |left, right| left.cmp(&right).is_le());
binary_bool_export!(fz_op_gt_bb, |left, right| left.cmp(&right).is_gt());
binary_bool_export!(fz_op_gte_bb, |left, right| left.cmp(&right).is_ge());

macro_rules! ref_equality_export {
    ($name:ident, $mode:expr, $expected:expr) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn $name(
            process: *mut Process,
            left_word: u64,
            left_kind: u64,
            right_word: u64,
            right_kind: u64,
        ) -> u64 {
            let left = Stored {
                word: left_word,
                kind: left_kind,
            }
            .value("runtime equality lhs");
            let right = Stored {
                word: right_word,
                kind: right_kind,
            }
            .value("runtime equality rhs");
            u64::from(values_equal(process, left, right, $mode) == $expected)
        }
    };
}

ref_equality_export!(fz_op_eq, NumericMode::Widening, true);
ref_equality_export!(fz_op_neq, NumericMode::Widening, false);
ref_equality_export!(fz_op_identical, NumericMode::Strict, true);
ref_equality_export!(fz_op_not_identical, NumericMode::Strict, false);

fn values_equal(process: *mut Process, a: AnyValue, b: AnyValue, mode: NumericMode) -> bool {
    let process = unsafe { &*process };
    let registry = process.heap.schemas_registry();
    let schemas = registry.borrow();
    TermComparator::new(&process.node, &schemas).equal(a, b, mode)
}

fn compare_values(process: *mut Process, a: AnyValue, b: AnyValue, mode: NumericMode) -> std::cmp::Ordering {
    let process = unsafe { &*process };
    let registry = process.heap.schemas_registry();
    let schemas = registry.borrow();
    TermComparator::new(&process.node, &schemas).compare(a, b, mode)
}

/// Ordering between a dynamic `AnyValueRef` and an unboxed payload, with no
/// allocation on either side — the ordering counterpart to
/// [`fz_value_eq_raw_const`].
///
/// An `AnyValueRef` for an integer or float is a POINTER to a heap scalar box,
/// so handing an unboxed operand to a ref-taking function forces an allocation.
/// Comparison never needs a value's identity, only its kind and payload, so
/// codegen passes those directly. `swap` says the unboxed side was
/// the right-hand operand, so the caller does not have to negate the result.
#[unsafe(no_mangle)]
pub extern "C" fn fz_value_cmp_raw_const(
    process: *mut Process,
    ref_word: u64,
    kind_tag: u32,
    raw: u64,
    swap: u32,
) -> i64 {
    let dynamic = any_value_from_ref_word(ref_word, "fz_value_cmp_raw_const");
    let Some(kind) = ValueKind::new(kind_tag as u8) else {
        panic!("fz_value_cmp_raw_const: unknown operand kind {kind_tag}");
    };
    let Some(unboxed) = AnyValue::decode_parts(raw, kind.tag()) else {
        panic!("fz_value_cmp_raw_const: undecodable operand of kind {kind:?}");
    };
    let (left, right) = if swap == 0 {
        (dynamic, unboxed)
    } else {
        (unboxed, dynamic)
    };
    compare_values(process, left, right, NumericMode::Widening) as i64
}

/// Widen numeric values recursively for `==`; map keys remain strict.
#[unsafe(no_mangle)]
pub extern "C" fn fz_value_eq_widening_ref(
    process: *mut Process,
    a_word: u64,
    a_kind: u64,
    b_word: u64,
    b_kind: u64,
) -> u64 {
    let a = Stored {
        word: a_word,
        kind: a_kind,
    }
    .value("fz_value_eq_widening_ref lhs");
    let b = Stored {
        word: b_word,
        kind: b_kind,
    }
    .value("fz_value_eq_widening_ref rhs");
    u64::from(values_equal(process, a, b, NumericMode::Widening))
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_value_eq_ref(process: *mut Process, a_word: u64, a_kind: u64, b_word: u64, b_kind: u64) -> u64 {
    let a = Stored {
        word: a_word,
        kind: a_kind,
    }
    .value("fz_value_eq_ref lhs");
    let b = Stored {
        word: b_word,
        kind: b_kind,
    }
    .value("fz_value_eq_ref rhs");
    u64::from(values_equal(process, a, b, NumericMode::Strict))
}

// UTF-8 runtime support.

/// Length of the first valid UTF-8 codepoint, or the byte offset at which its
/// prefix becomes invalid. An error at `bytes.len()` means the prefix is
/// incomplete rather than contradicted by a byte in hand.
fn utf8_prefix(bytes: &[u8]) -> Result<usize, usize> {
    let Some(&first) = bytes.first() else {
        return Ok(0);
    };
    match first {
        0x00..=0x7f => Ok(1),
        0xc2..=0xdf => utf8_byte_in(bytes, 1, 0x80, 0xbf).map(|()| 2),
        0xe0 => utf8_byte_in(bytes, 1, 0xa0, 0xbf)
            .and_then(|()| utf8_continuation(bytes, 2))
            .map(|()| 3),
        0xe1..=0xec | 0xee..=0xef => utf8_continuation(bytes, 1)
            .and_then(|()| utf8_continuation(bytes, 2))
            .map(|()| 3),
        0xed => utf8_byte_in(bytes, 1, 0x80, 0x9f)
            .and_then(|()| utf8_continuation(bytes, 2))
            .map(|()| 3),
        0xf0 => utf8_byte_in(bytes, 1, 0x90, 0xbf)
            .and_then(|()| utf8_continuation(bytes, 2))
            .and_then(|()| utf8_continuation(bytes, 3))
            .map(|()| 4),
        0xf1..=0xf3 => utf8_continuation(bytes, 1)
            .and_then(|()| utf8_continuation(bytes, 2))
            .and_then(|()| utf8_continuation(bytes, 3))
            .map(|()| 4),
        0xf4 => utf8_byte_in(bytes, 1, 0x80, 0x8f)
            .and_then(|()| utf8_continuation(bytes, 2))
            .and_then(|()| utf8_continuation(bytes, 3))
            .map(|()| 4),
        _ => Err(0),
    }
}

fn utf8_continuation(bytes: &[u8], index: usize) -> Result<(), usize> {
    utf8_byte_in(bytes, index, 0x80, 0xbf)
}

fn utf8_byte_in(bytes: &[u8], index: usize, min: u8, max: u8) -> Result<(), usize> {
    match bytes.get(index) {
        Some(byte) if (min..=max).contains(byte) => Ok(()),
        Some(_) => Err(index),
        None => Err(bytes.len()),
    }
}

/// Returns 1 if the bitstring's bytes are valid UTF-8 AND the
/// bit-length is byte-aligned (multiple of 8). Returns 0 otherwise.
///
/// Bitstrings that aren't byte-aligned cannot be UTF-8 (UTF-8 is a
/// byte-oriented encoding); this function rejects them up front.
///
/// Called by Utf8.valid?, Utf8.from_bytes and Utf8.from_bytes!.
///
/// # Safety
/// The caller must pass the tagged word of a bitstring, which the extern's
/// `bitstring` parameter proves.
#[unsafe(no_mangle)]
pub extern "C" fn fz_bitstring_valid_utf8(bs_bits: u64) -> i64 {
    let bin = unsafe { Bin::of_binary(bs_bits) };
    if !bin.bit_len().is_multiple_of(8) {
        return 0;
    }
    let slice = bin.bytes();
    let mut offset = 0;
    while offset < slice.len() {
        let Ok(width) = utf8_prefix(&slice[offset..]) else {
            return 0;
        };
        offset += width;
    }
    1
}

/// Describes the first UTF-8 codepoint in a byte-aligned binary.
///
/// A positive result is the valid codepoint's byte length. Zero means empty.
/// A negative result encodes the first invalid byte offset as `-offset - 1`;
/// an offset equal to the input length means an incomplete prefix. This scalar
/// contract lets `Utf8.next/1` return the original suffix without allocating
/// in the runtime.
#[unsafe(no_mangle)]
pub extern "C" fn fz_bitstring_utf8_prefix(bs_bits: u64) -> i64 {
    let bin = unsafe { Bin::of_binary(bs_bits) };
    if !bin.bit_len().is_multiple_of(8) {
        return -1;
    }
    match utf8_prefix(bin.bytes()) {
        Ok(width) => width as i64,
        Err(offset) => -(offset as i64) - 1,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_matcher_map_get_ref(
    process: *mut Process,
    map_ref_word: u64,
    key_word: u64,
    key_kind: u64,
) -> u64 {
    let map = any_value_ref_from_word(map_ref_word, "fz_matcher_map_get_ref map");
    let key = Stored {
        word: key_word,
        kind: key_kind,
    }
    .value("fz_matcher_map_get_ref key");
    (unsafe { &mut *process })
        .heap
        .read_map_value(map, key)
        .unwrap_or_else(AnyValueRef::null)
        .raw_word()
}

/// Whether `subject` is a binary equal to the literal of `bit_len` bits at
/// `bytes`: the receive matcher's test for a binary literal pattern. Any
/// bitstring-like subject is compared by `Bin` equality; a non-binary is not
/// equal.
///
/// # Safety
/// `bytes` must be readable for `bit_len` bits. `subject` is treated as an
/// opaque AnyValue.
#[unsafe(no_mangle)]
pub extern "C" fn fz_binary_equals_literal(subject: u64, bytes: *const u8, bit_len: u64) -> u32 {
    (is_bitstring_like(subject) && unsafe { Bin::of_binary(subject) } == Bin::new(bytes, bit_len)) as u32
}

/// Identity at the bits level — the brand is a type-system label, not
/// a runtime tag. The planner must have already certified that `b`
/// names a bitstring (typically a fresh `ConstBitstring` or the
/// output of `fz_bitstring_valid_utf8` after a positive check).
/// Returned bits are the input bits.
///
/// Exists as a named seam so the planner can attach the `utf8` brand to
/// the value's Descr at this call site (the type rule for the L3
/// desugaring pass references this extern by name).
#[unsafe(no_mangle)]
pub extern "C" fn fz_brand_bitstring_as_utf8(b: u64) -> u64 {
    b
}

#[cfg(test)]
#[path = "ir_runtime_test.rs"]
mod ir_runtime_test;
