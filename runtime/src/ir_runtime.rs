//! Runtime helpers for the fz JIT — the `extern "C"` fns the generated
//! Cranelift code calls into. Lifted out of ir_codegen.rs by fz-ul4.23.4
//! so that ir_codegen can become purely codegen and a future AOT backend
//! can link against the same FFI surface without dragging the JIT module
//! along.
//!
//! This file holds the **arith / cmp / eq** cluster (fz-ul4.23.4.1)
//! and the **alloc** cluster (fz-ul4.23.4.7). Other clusters land in
//! sibling tickets:
//!   .8  map     (fz_map_*, fz_key_*)
//!   .9  bitstring (fz_bs_*, decode_*/encode_* bit helpers)
//!   .11 closure (fz_closure_*, fz_tail_closure)
//!   .12 concurrency (fz_spawn, fz_self, fz_send, fz_receive_attempt)
//!   .13 halt/print (fz_halt, fz_dbg_value)
//!
//! All fns here have unstable `extern "C"` ABI — they're called by
//! Cranelift-emitted code via the symbol-binding list in
//! `ir_codegen::compile`. Do not reorder args or change return types
//! without updating the matching `declare_function` signatures.

use crate::any_value::AnyValueRef;
use crate::any_value::ValueKind;
use crate::process::Process;

static NIL_ATOM_REF_SLOT: u64 = crate::any_value::NIL_ATOM_ID as u64;

fn any_value_from_heap_object_word(bits: u64) -> crate::any_value::AnyValue {
    crate::any_value::AnyValue::decode_tagged_heap_bits(bits)
        .unwrap_or_else(|| panic!("expected strict tagged heap value, got {bits:#x}"))
}

fn any_value_ref_from_word(word: u64, context: &str) -> AnyValueRef {
    AnyValueRef::from_raw_word(word)
        .unwrap_or_else(|err| panic!("{context}: invalid any value ref {word:#x}: {err:?}"))
}

fn any_value_from_ref_word(word: u64, context: &str) -> crate::any_value::AnyValue {
    use crate::any_value::{AnyValue, ValueKind};
    let value = any_value_ref_from_word(word, context);
    if value.is_empty_list() {
        return AnyValue::empty_list();
    }
    match value.tag() {
        ValueKind::NULL => AnyValue::null(),
        ValueKind::INT => AnyValue::int(value.load_int().expect(context)),
        ValueKind::FLOAT => AnyValue::float(value.load_float().expect(context)),
        ValueKind::ATOM => AnyValue::atom(value.load_atom().expect(context) as u32),
        ValueKind::LIST => AnyValue::heap_ptr(value.list_addr().expect(context), ValueKind::LIST),
        ValueKind::MAP => AnyValue::heap_ptr(value.map_addr().expect(context), ValueKind::MAP),
        ValueKind::STRUCT => {
            AnyValue::heap_ptr(value.struct_addr().expect(context), ValueKind::STRUCT)
        }
        ValueKind::CLOSURE => {
            AnyValue::heap_ptr(value.closure_addr().expect(context), ValueKind::CLOSURE)
        }
        ValueKind::BITSTRING => {
            AnyValue::heap_ptr(value.bitstring_addr().expect(context), ValueKind::BITSTRING)
        }
        ValueKind::PROCBIN => {
            AnyValue::heap_ptr(value.procbin_addr().expect(context), ValueKind::PROCBIN)
        }
        ValueKind::RESOURCE => {
            AnyValue::heap_ptr(value.resource_addr().expect(context), ValueKind::RESOURCE)
        }
        _ => unreachable!("AnyValueRef tag set is exhaustive"),
    }
}

fn heap_object_word_from_ref_word(word: u64, context: &str) -> u64 {
    let value = any_value_from_ref_word(word, context);
    value
        .heap_object_word()
        .unwrap_or_else(|| panic!("{context}: expected heap ref"))
}

fn heap_ref_word(tag: ValueKind, addr: *const u8) -> u64 {
    AnyValueRef::from_heap_object(tag, addr)
        .expect("heap object ref")
        .raw_word()
}

fn closure_ref_word_from_bits(bits: u64) -> u64 {
    let addr = crate::any_value::closure_addr_from_tagged(bits).expect("closure heap bits");
    heap_ref_word(ValueKind::CLOSURE, addr)
}

fn closure_addr_from_ref_word(word: u64, context: &str) -> *mut u8 {
    any_value_ref_from_word(word, context)
        .closure_addr()
        .expect(context)
}

fn map_ref_word_from_bits(bits: u64) -> u64 {
    let addr = crate::any_value::map_addr_from_tagged(bits).expect("map heap bits");
    heap_ref_word(ValueKind::MAP, addr)
}

fn process_atom_id(process: *mut Process, name: &str) -> u32 {
    let process = unsafe { &mut *process };
    if let Some(id) = process
        .atom_names
        .iter()
        .position(|existing| existing == name)
    {
        return id as u32;
    }
    let id = process.atom_names.len() as u32;
    process.atom_names.push(name.to_string());
    id
}

fn alloc_stat_entries(
    process: *mut Process,
    entries: &mut Vec<(crate::any_value::AnyValue, crate::any_value::AnyValue)>,
    prefix: &str,
    stat: crate::heap::AllocStat,
) {
    let allocs_key = process_atom_id(process, &format!("{prefix}_allocs"));
    let bytes_key = process_atom_id(process, &format!("{prefix}_bytes"));
    entries.push((
        crate::any_value::AnyValue::atom(allocs_key),
        crate::any_value::AnyValue::int(stat.allocs as i64),
    ));
    entries.push((
        crate::any_value::AnyValue::atom(bytes_key),
        crate::any_value::AnyValue::int(stat.bytes as i64),
    ));
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_process_heap_alloc_stats(process: *mut Process) -> u64 {
    let p = unsafe { &mut *process };
    let snapshot = p.heap.alloc_stats_snapshot();
    let scheduler_yields = p.scheduler_yields;
    let interpreter_yields = p.interpreter_yields;
    let reductions_remaining = p.reductions_remaining;
    let reductions_per_quantum = p.reductions_per_quantum;
    let reductions_executed = p.reductions_executed;
    let reduction_yields = p.reduction_yields;
    let allocation_pressure_yields = p.allocation_pressure_yields;
    let yield_reasons = p.yield_reasons;
    let max_yield_continuation_bytes = p.max_yield_continuation_bytes;
    let min_yield_continuation_margin_before_bytes = p.min_yield_continuation_margin_before_bytes;
    let min_yield_continuation_margin_after_bytes = p.min_yield_continuation_margin_after_bytes;
    let mut entries = Vec::with_capacity(33);
    entries.push((
        crate::any_value::AnyValue::atom(process_atom_id(process, "allocs")),
        crate::any_value::AnyValue::int(snapshot.total.allocs as i64),
    ));
    entries.push((
        crate::any_value::AnyValue::atom(process_atom_id(process, "bytes")),
        crate::any_value::AnyValue::int(snapshot.total.bytes as i64),
    ));
    alloc_stat_entries(process, &mut entries, "list_cons", snapshot.list_cons);
    alloc_stat_entries(process, &mut entries, "struct", snapshot.struct_);
    alloc_stat_entries(process, &mut entries, "closure", snapshot.closure);
    alloc_stat_entries(process, &mut entries, "map", snapshot.map);
    alloc_stat_entries(process, &mut entries, "bitstring", snapshot.bitstring);
    alloc_stat_entries(process, &mut entries, "procbin", snapshot.procbin);
    alloc_stat_entries(process, &mut entries, "scalar_box", snapshot.scalar_box);
    alloc_stat_entries(process, &mut entries, "frame", snapshot.frame);
    alloc_stat_entries(process, &mut entries, "resource", snapshot.resource);
    alloc_stat_entries(process, &mut entries, "other", snapshot.other);
    entries.push((
        crate::any_value::AnyValue::atom(process_atom_id(process, "scheduler_yields")),
        crate::any_value::AnyValue::int(scheduler_yields as i64),
    ));
    entries.push((
        crate::any_value::AnyValue::atom(process_atom_id(process, "interpreter_yields")),
        crate::any_value::AnyValue::int(interpreter_yields as i64),
    ));
    entries.push((
        crate::any_value::AnyValue::atom(process_atom_id(process, "reductions_remaining")),
        crate::any_value::AnyValue::int(reductions_remaining as i64),
    ));
    entries.push((
        crate::any_value::AnyValue::atom(process_atom_id(process, "reductions_per_quantum")),
        crate::any_value::AnyValue::int(reductions_per_quantum as i64),
    ));
    entries.push((
        crate::any_value::AnyValue::atom(process_atom_id(process, "reductions_executed")),
        crate::any_value::AnyValue::int(reductions_executed as i64),
    ));
    entries.push((
        crate::any_value::AnyValue::atom(process_atom_id(process, "reduction_yields")),
        crate::any_value::AnyValue::int(reduction_yields as i64),
    ));
    entries.push((
        crate::any_value::AnyValue::atom(process_atom_id(process, "allocation_pressure_yields")),
        crate::any_value::AnyValue::int(allocation_pressure_yields as i64),
    ));
    entries.push((
        crate::any_value::AnyValue::atom(process_atom_id(process, "yield_reasons")),
        crate::any_value::AnyValue::int(yield_reasons as i64),
    ));
    entries.push((
        crate::any_value::AnyValue::atom(process_atom_id(process, "max_yield_continuation_bytes")),
        crate::any_value::AnyValue::int(max_yield_continuation_bytes as i64),
    ));
    entries.push((
        crate::any_value::AnyValue::atom(process_atom_id(
            process,
            "min_yield_continuation_margin_before_bytes",
        )),
        crate::any_value::AnyValue::int(min_yield_continuation_margin_before_bytes as i64),
    ));
    entries.push((
        crate::any_value::AnyValue::atom(process_atom_id(
            process,
            "min_yield_continuation_margin_after_bytes",
        )),
        crate::any_value::AnyValue::int(min_yield_continuation_margin_after_bytes as i64),
    ));
    map_ref_word_from_bits((unsafe { &mut *process }).heap.alloc_map_slots(&entries))
}

fn map_bits_from_ref_word(word: u64, context: &str) -> u64 {
    let map = any_value_ref_from_word(word, context);
    if map.tag() == ValueKind::NULL {
        return 0;
    }
    crate::any_value::heap_object_word(
        map.map_addr().expect(context),
        crate::any_value::ValueKind::MAP,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_ref_tag(ref_word: u64) -> u8 {
    any_value_ref_from_word(ref_word, "fz_ref_tag").tag().tag()
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
    unsafe { crate::any_value::struct_schema_id(addr.cast_const()) }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_truthy_ref(ref_word: u64) -> u8 {
    let value = any_value_ref_from_word(ref_word, "fz_truthy_ref");
    if value.tag() != ValueKind::ATOM {
        return 1;
    }
    let atom = value.load_atom().expect("fz_truthy_ref atom");
    (atom != crate::any_value::FALSE_ATOM_ID as u64 && atom != crate::any_value::NIL_ATOM_ID as u64)
        as u8
}

fn ref_load_atom_impl(ref_word: u64) -> u64 {
    any_value_ref_from_word(ref_word, "fz_ref_load_atom")
        .load_atom()
        .expect("fz_ref_load_atom")
}

fn box_scalar_for_any(process: *mut Process, raw: u64, tag: ValueKind) -> u64 {
    let slot = (unsafe { &mut *process }).heap.alloc_kind(
        crate::heap::HeapAllocKind::ScalarBox,
        std::mem::size_of::<u64>(),
    ) as *mut u64;
    unsafe {
        std::ptr::write(slot, raw);
    }
    AnyValueRef::from_scalar_slot(tag, slot as *const u64)
        .expect("scalar ref")
        .raw_word()
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_box_int_for_any(process: *mut Process, raw: i64) -> u64 {
    box_scalar_for_any(process, raw as u64, ValueKind::INT)
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_box_float_for_any(process: *mut Process, raw: f64) -> u64 {
    box_scalar_for_any(process, raw.to_bits(), ValueKind::FLOAT)
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_box_atom_for_any(process: *mut Process, raw: u64) -> u64 {
    box_scalar_for_any(process, raw, ValueKind::ATOM)
}

// ===== Halt + print cluster (fz-ul4.23.4.13) =====

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_dbg_value_ref(process: *mut Process, ref_word: u64) {
    let value = any_value_from_ref_word(ref_word, "fz_dbg_value_ref");
    crate::emit_print_line(
        process,
        crate::any_value::debug::render_value(process, value),
    );
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_dbg_value(process: *mut Process, ref_word: u64) -> u64 {
    fz_dbg_value_ref(process, ref_word);
    ref_word
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_dynamic_float_arith_unsupported() -> u64 {
    panic!("dynamic float arithmetic needs a typed float result carrier")
}

/// fz-ul4.27.22.3 — typed halt for narrow-int seams. The cont chain
/// carries a raw i64 all the way to halt-cont's RawInt body; no
/// unboxing — value is already a machine int.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_halt_implicit_i64(process: *mut Process, val: i64) {
    (unsafe { &mut *process }).halt_value = val;
}

/// fz-ul4.27.22.3 — typed halt for narrow-float seams. Mirrors
/// fz_halt's Boxed-float branch: store `to_bits() as i64` so tests
/// can round-trip via f64::from_bits.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_halt_implicit_f64(process: *mut Process, val: f64) {
    (unsafe { &mut *process }).halt_value = val.to_bits() as i64;
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_halt_implicit_ref(process: *mut Process, ref_word: u64) {
    (unsafe { &mut *process }).halt_value =
        halt_value_from_slot(any_value_from_ref_word(ref_word, "fz_halt_implicit_ref"));
}

fn halt_value_from_slot(value: crate::any_value::AnyValue) -> i64 {
    use crate::any_value::ValueKind;
    match value.kind() {
        ValueKind::INT => value.raw() as i64,
        ValueKind::ATOM => value.raw() as i64,
        ValueKind::FLOAT => value.raw() as i64,
        ValueKind::NULL => 0,
        kind if kind.is_heap() => value.heap_object_word().unwrap_or(value.raw()) as i64,
        _ => value.raw() as i64,
    }
}

// ===== Concurrency cluster (fz-ul4.23.4.12) =====

/// fz-ul4.19.2: scheduler-bound builtins.
///
/// Both consume a Runtime installed in TLS by Runtime::run_until_idle.
/// Calling either outside the scheduler path panics with a clear message.
///
/// Borrow the execution context a BIF reaches scheduler services through.
/// The owning scheduler installs it on the Process (`ctx.2`); it outlives any
/// FFI call made under this process.
#[inline]
unsafe fn process_ctx<'a>(process: *mut Process) -> &'a crate::exec_ctx::ExecCtx {
    let ctx = unsafe { (*process).ctx };
    debug_assert!(!ctx.is_null(), "process.ctx installed before BIF dispatch");
    unsafe { &*ctx }
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_spawn_ref(process: *mut Process, closure_ref_word: u64) -> u64 {
    let ctx = unsafe { process_ctx(process) };
    (ctx.spawn.expect("spawn callback installed"))(process, ctx.scheduler, closure_ref_word) as u64
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_spawn_opt_ref(
    process: *mut Process,
    closure_ref_word: u64,
    min_heap_size: u64,
) -> u64 {
    let ctx = unsafe { process_ctx(process) };
    (ctx.spawn_opt.expect("spawn_opt callback installed"))(
        process,
        ctx.scheduler,
        closure_ref_word,
        min_heap_size as u32,
    ) as u64
}

/// fz-swt.10 — `make_resource(payload, dtor)` runtime BIF, callable from
/// the JIT/AOT path. The payload is a raw integer handle; the destructor
/// crosses as an opaque `AnyValueRef` closure word. Returns the tagged
/// `TAG_RESOURCE` stub on the current process heap.
///
/// Dtor resolution requires walking the closure body's IR to find the
/// underlying `Prim::Extern`, so we delegate to the binary-side hook
/// (the runtime crate has no IR Module). The same hook is installed for
/// both interp and JIT/AOT execution — the symbol path is therefore
/// uniform across all three legs (see fz-swt.10's `MakeResourceHook`).
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_make_resource_ref(
    process: *mut Process,
    payload_raw: u64,
    dtor_ref: u64,
) -> u64 {
    let ctx = unsafe { process_ctx(process) };
    (ctx.make_resource.expect("make_resource callback installed"))(
        process,
        ctx.module,
        payload_raw,
        dtor_ref,
    )
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_self_raw(process: *mut Process) -> u64 {
    (unsafe { &mut *process }).pid as u64
}

/// fz-ht5 — process-global monotonic counter feeding `fz_make_ref`.
/// Starts at 1 so 0 can remain a "no ref" sentinel if a future ticket
/// needs one. AtomicU64 + Relaxed is sufficient under single-worker
/// today and remains correct under future multi-worker.
static FZ_NEXT_REF: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

#[unsafe(no_mangle)]
pub extern "C" fn fz_make_ref_raw() -> u64 {
    FZ_NEXT_REF.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

/// fz_send_ref(receiver_pid, msg_ref) -> msg_ref.
///
/// `send` is an `any` boundary: callers box known scalars before calling, then
/// the scheduler/mailbox moves the one-word any value ref until a matcher or
/// receiver unwraps it.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_send_ref(
    process: *mut Process,
    receiver_pid_bits: u64,
    msg_ref_word: u64,
) -> u64 {
    let receiver_pid = receiver_pid_bits as u32;
    let _ = any_value_ref_from_word(msg_ref_word, "fz_send_ref message");
    let ctx = unsafe { process_ctx(process) };
    (ctx.send.expect("send callback installed"))(
        process,
        ctx.scheduler,
        receiver_pid,
        msg_ref_word,
    );
    msg_ref_word
}

/// Plain `receive()` park entry. Caller has already built the continuation
/// closure template. We install it as a one-clause ParkRecord with an
/// accept-any matcher, so the scheduler wakes it through the same
/// `runnable_closure` path as selective receive.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_receive_park(process: *mut Process, cont_closure_bits: u64) -> *mut u8 {
    use crate::{process::ProcessState, scheduler_hooks::YIELD_PTR};
    let p = unsafe { &mut *process };
    p.parked_matched = Some(Box::new(crate::park::ParkRecord {
        matcher_fn: crate::park::match_any_message,
        pinned: Vec::new(),
        clause_bodies: vec![closure_addr_from_ref_word(
            cont_closure_bits,
            "fz_receive_park cont",
        )],
        clause_bound_counts: vec![1],
        bound_arity: 1,
        after_deadline_ms: None,
        after_cont: std::ptr::null_mut(),
        after_timer_id: None,
    }));
    p.state = if p.mailbox.is_empty() {
        ProcessState::Blocked
    } else {
        ProcessState::Ready
    };
    YIELD_PTR as *mut u8
}

/// fz-yxs/fz-st5 — selective receive park entry. Called by JIT/AOT
/// codegen at the `Term::ReceiveMatched` seam after the matcher fn,
/// pinned snapshot, clause-body table, and (optional) after-cont
/// closure have been laid out by `build_park_record` (B3).
///
/// Args:
/// - `matcher_fn_bits`: raw pointer to the codegen'd matcher fn.
/// - `pinned_ptr` / `n_pinned`: array of `AnyValueRef` pinned matcher
///   values. `n_pinned` is the logical entry count.
/// - `clause_bodies_ptr` / `n_clauses`: array of clause-body closure
///   pointers (one per source clause, in declaration order).
/// - `clause_bound_counts_ptr`: array of per-clause bound-variable counts.
/// - `bound_arity`: max bound-var count across clauses.
/// - `after_deadline_or_neg1`: absolute deadline in millis, or `-1`
///   when there is no after (no timer; matcher hit is the only way
///   the receiver wakes).
/// - `after_cont_bits`: after-body closure pointer, or `0` when no
///   after clause.
///
/// Returns the YIELD sentinel so the trampoline parks the task.
#[unsafe(no_mangle)]
#[allow(clippy::too_many_arguments, clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_receive_park_matched(
    process: *mut Process,
    matcher_fn_bits: u64,
    pinned_ptr: *const crate::any_value::AnyValueRef,
    n_pinned: u64,
    clause_bodies_ptr: *const u64,
    n_clauses: u64,
    clause_bound_counts_ptr: *const u64,
    bound_arity: u32,
    after_deadline_or_neg1: i64,
    after_cont_bits: u64,
) -> *mut u8 {
    use crate::park::{MatcherFn, ParkRecord};
    use crate::{process::ProcessState, scheduler_hooks::YIELD_PTR};

    let matcher_fn: MatcherFn = unsafe { std::mem::transmute(matcher_fn_bits as usize) };
    // fz-70q.3 — codegen passes `null` for `pinned_ptr` / `clause_bodies_ptr`
    // when the corresponding count is 0. `slice::from_raw_parts` rejects
    // null even with len 0 (its safety contract requires a valid aligned
    // pointer), so guard the zero-len case explicitly.
    let pinned: Vec<crate::any_value::AnyValueRef> = if n_pinned == 0 {
        Vec::new()
    } else {
        unsafe { std::slice::from_raw_parts(pinned_ptr, n_pinned as usize).to_vec() }
    };
    let clause_bodies: Vec<*mut u8> = if n_clauses == 0 {
        Vec::new()
    } else {
        unsafe {
            std::slice::from_raw_parts(clause_bodies_ptr, n_clauses as usize)
                .iter()
                .map(|&bits| {
                    closure_addr_from_ref_word(bits, "fz_receive_park_matched clause body")
                })
                .collect()
        }
    };
    let clause_bound_counts: Vec<u16> = if n_clauses == 0 {
        Vec::new()
    } else if clause_bound_counts_ptr.is_null() {
        vec![bound_arity as u16; n_clauses as usize]
    } else {
        unsafe { std::slice::from_raw_parts(clause_bound_counts_ptr, n_clauses as usize) }
            .iter()
            .map(|&n| n as u16)
            .collect()
    };
    let after_deadline_ms = if after_deadline_or_neg1 < 0 {
        None
    } else {
        Some(after_deadline_or_neg1 as u64)
    };

    let p = unsafe { &mut *process };
    let after_timer_id = match after_deadline_ms {
        Some(after_ms) => crate::exec_ctx::timer_schedule(p, p.pid, after_ms),
        None => None,
    };
    let after_cont = if after_cont_bits == 0 {
        std::ptr::null_mut()
    } else {
        closure_addr_from_ref_word(after_cont_bits, "fz_receive_park_matched after cont")
    };

    let park = ParkRecord {
        matcher_fn,
        pinned,
        clause_bodies,
        clause_bound_counts,
        bound_arity: bound_arity as u16,
        after_deadline_ms,
        after_cont,
        after_timer_id,
    };

    p.parked_matched = Some(Box::new(park));
    // Symmetric to fz_receive_park: if any message is already in the
    // mailbox we mark Ready so the scheduler runs an initial scan via
    // the matcher path. The actual scan happens in the scheduler when
    // it sees parked_matched.is_some() on a Ready task.
    p.state = if p.mailbox.is_empty() {
        ProcessState::Blocked
    } else {
        ProcessState::Ready
    };
    YIELD_PTR as *mut u8
}

/// Boundary-reporting mid-flight yield entry.
///
/// Generated/interpreted code reports the scheduler continuation, signed
/// reductions left in the turn, and the reason bits that caused the yield. The
/// scheduler knows how many reductions it granted, so it derives burned work at
/// the boundary instead of syncing against the hot-path budget cell.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_yield_mid_flight_report(
    process: *mut Process,
    cont_closure_bits: u64,
    remaining_reductions: i32,
    reason: u32,
) -> *mut u8 {
    use crate::scheduler_hooks::YIELD_PTR;
    let p = unsafe { &mut *process };
    p.scheduler_yields = p.scheduler_yields.saturating_add(1);
    // Allocation-pressure reasons already stand on `p.yield_reasons`;
    // finish_yield_report folds them in when attributing the cause.
    p.finish_yield_report(remaining_reductions, reason as u8);
    let closure_addr =
        closure_addr_from_ref_word(cont_closure_bits, "fz_yield_mid_flight_report cont");
    let closure_bits = crate::any_value::heap_object_word(closure_addr, ValueKind::CLOSURE);
    let continuation_bytes = crate::any_value::object_size(closure_bits);
    let margin_after = p.heap.bytes_remaining_in_block();
    p.note_yield_continuation_allocation(continuation_bytes, margin_after);
    p.set_runnable_closure(closure_addr);
    YIELD_PTR as *mut u8
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_yield_slow_path_begin(process: *mut Process) {
    let p = unsafe { &mut *process };
    p.begin_yield_continuation_allocation(p.heap.bytes_remaining_in_block());
}

// ===== Closure cluster (fz-ul4.23.4.11) =====
//
// Closures are schema-backed environments with a raw code pointer at +8.
// Invocation is a call_indirect through that code pointer; captures are
// ordinary env fields read and written through the runtime accessors.

/// Allocate a closure heap object with `captured_count` capture slots.
/// The runtime stores the body pointer while the tagged closure ref is still
/// opaque to generated code; callers populate captures through accessors.
/// `halt_kind` (fz-ul4.27.22.6) is packed into the closure header's
/// `flags` so `fz_spawn_entry` can pick the matching halt-cont singleton
/// at task launch.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_alloc_closure(
    process: *mut Process,
    callee_fn_id: u32,
    captured_count: u32,
    halt_kind: u32,
    body_addr: u64,
) -> u64 {
    FRAME_ALLOC_COUNT.with(|c| c.set(c.get() + 1));
    let bits = (unsafe { &mut *process }).heap.alloc_closure_slots(
        callee_fn_id,
        captured_count as usize,
        halt_kind as u16,
    );
    let addr = crate::any_value::closure_addr_from_tagged(bits).expect("new closure bits");
    unsafe { std::ptr::write(addr.add(8) as *mut u64, body_addr) };
    closure_ref_word_from_bits(bits)
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_closure_code_ref(closure_ref_word: u64) -> u64 {
    if is_lazy_cont_ref(closure_ref_word) {
        return unsafe { *(lazy_cont_ptr(closure_ref_word) as *const u64) };
    }
    let addr = closure_addr_from_ref_word(closure_ref_word, "fz_closure_code_ref closure");
    unsafe { crate::any_value::closure_fn_ptr(addr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_closure_halt_kind_ref(closure_ref_word: u64) -> u32 {
    let addr = closure_addr_from_ref_word(closure_ref_word, "fz_closure_halt_kind_ref closure");
    unsafe { crate::any_value::closure_halt_kind(addr) as u32 }
}

/// fz-cps.1.11 — return the per-Process singleton halt-cont closure.
/// Lazily initialized on first call using the provided
/// `halt_cont_body_addr` (taken at each call site via `func_addr`).
/// JIT path: `make_process` pre-populates the singleton; this is a
/// hot-path direct return. AOT path: the singleton may be null at
/// first call, so this allocates with the supplied body addr.
/// Reusing one singleton instead of allocating per uniform→native
/// call site preserves test invariants that count heap allocations
/// exactly (`gc_traces_closure_captured_via_jit`).
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_get_halt_cont(
    process: *mut Process,
    halt_cont_body_addr: u64,
    kind: u32,
) -> u64 {
    // fz-ul4.27.22.3 — `kind` selects which of three per-Process halt-cont
    // singletons to return (0=ValueRef, 1=RawInt, 2=RawF64). Each holds a
    // body whose Tail-CC sig matches its repr. Producer's Term::Return
    // uses sig (return_repr, i64); the code pointer at +8 must agree.
    let p = unsafe { &mut *process };
    let slot = kind as usize;
    if !p.halt_cont_singletons[slot].is_null() {
        return heap_ref_word(
            ValueKind::CLOSURE,
            p.halt_cont_singletons[slot] as *const u8,
        );
    }
    let closure_schema = p.heap.closure_schema_id(0);
    let mut buf = crate::process::AlignedClosureStorage::zeroed();
    let base = buf.as_ptr();
    unsafe {
        std::ptr::write(base as *mut u32, closure_schema);
        std::ptr::write(
            base.add(4) as *mut u32,
            crate::any_value::closure_flags_pack(0, kind as u16) as u32,
        );
        std::ptr::write(base.add(8) as *mut u64, halt_cont_body_addr);
    }
    p.halt_cont_singletons[slot] = base;
    p.static_closure_bufs.push(buf);
    heap_ref_word(
        ValueKind::CLOSURE,
        p.halt_cont_singletons[slot] as *const u8,
    )
}

/// fz-cps.1.7 — return the per-Process static zero-capture singleton for
/// the given closure spec id. Populated at `make_process` time from
/// `CompiledModule::static_closure_targets`. Cheaper than
/// `fz_alloc_closure(fid, 0, body_addr)` at every `Prim::MakeClosure(fid, [])`
/// site. See docs/cps-in-clif.md §8.2 acceptance: "Module-init region produces
/// double/neg static closures exactly once."
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_get_static_closure(process: *mut Process, cl_sid: u32) -> u64 {
    let p = unsafe { &mut *process };
    let idx = cl_sid as usize;
    if idx < p.static_closures.len() {
        let ptr = p.static_closures[idx];
        if !ptr.is_null() {
            return heap_ref_word(ValueKind::CLOSURE, ptr as *const u8);
        }
    }
    panic!(
        "fz_get_static_closure: no singleton for cl_sid {} ({} entries)",
        cl_sid,
        p.static_closures.len()
    );
}

// ===== Bitstring cluster (fz-ul4.23.4.9) =====

fn bitstring_like_ptr(bits: u64) -> Option<*mut u8> {
    if matches!(
        bits & crate::any_value::TAG_MASK,
        crate::any_value::TAG_BITSTRING | crate::any_value::TAG_PROCBIN
    ) {
        Some(bits as *mut u8)
    } else {
        None
    }
}

fn bitstring_like_ptr_from_ref(word: u64) -> Option<*mut u8> {
    let value = AnyValueRef::from_raw_word(word).ok()?;
    match value.tag() {
        ValueKind::BITSTRING => value.bitstring_addr().ok().map(|addr| {
            crate::any_value::heap_object_word(addr, crate::any_value::ValueKind::BITSTRING)
                as *mut u8
        }),
        ValueKind::PROCBIN => value.procbin_addr().ok().map(|addr| {
            crate::any_value::heap_object_word(addr, crate::any_value::ValueKind::PROCBIN)
                as *mut u8
        }),
        _ => None,
    }
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_bs_begin(process: *mut Process) {
    (unsafe { &mut *process }).bs_builder = Some(crate::bitstr::BitWriter::new());
}

/// Write one field into the active builder. Field-type tags match the order
/// in `crate::bitstr::BitType`: Integer=0, Float=1, Binary=2, Bits=3, Utf8=4,
/// Utf16=5, Utf32=6. `size_present` distinguishes None (0) vs Some (1);
/// `size_value` is in size-units (multiplied by `unit` internally).
#[allow(clippy::too_many_arguments)]
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_bs_write_field_ref(
    process: *mut Process,
    value_ref: u64,
    ty_tag: u32,
    size_present: u32,
    size_value: u32,
    unit: u32,
    endian_tag: u32,
    signed: u32,
) {
    let value = any_value_from_ref_word(value_ref, "fz_bs_write_field_ref");
    fz_bs_write_field_value(
        process,
        value,
        ty_tag,
        size_present,
        size_value,
        unit,
        endian_tag,
        signed,
    );
}

#[allow(clippy::too_many_arguments)]
fn fz_bs_write_field_value(
    process: *mut Process,
    value: crate::any_value::AnyValue,
    ty_tag: u32,
    size_present: u32,
    size_value: u32,
    unit: u32,
    endian_tag: u32,
    signed: u32,
) {
    use crate::any_value::ValueKind;
    use crate::bitstr::BitType;
    let ty = decode_bit_type(ty_tag);
    let size = if size_present != 0 {
        Some(size_value)
    } else {
        None
    };
    let endian = decode_endian(endian_tag);
    // `signed` is irrelevant on write: two's-complement truncation produces
    // the same bit pattern for signed and unsigned at fixed width. The flag
    // is consumed on read (fz_bs_read_field) for sign extension.
    let _ = signed;
    {
        let w = (unsafe { &mut *process })
            .bs_builder
            .as_mut()
            .expect("fz_bs_write_field called without fz_bs_begin");
        match ty {
            BitType::Integer => {
                let n = match value.kind() {
                    ValueKind::INT => value.raw() as i64,
                    _ => panic!("integer bit field expects Int"),
                };
                let total = size.unwrap_or(8) * unit;
                assert!(total <= 64, "integer field too wide: {}", total);
                let masked = if total < 64 {
                    (n as u64) & ((1u64 << total) - 1)
                } else {
                    n as u64
                };
                let bswap = crate::bitstr::apply_endian_for_write(masked, total, endian);
                w.write_bits(bswap, total as usize);
            }
            BitType::Binary | BitType::Bits => {
                // Source must be a heap Bitstring (Vec(U8) lands in .11.14;
                // until then both Binary and Bits read from a Bitstring).
                let bits = value
                    .heap_object_word()
                    .unwrap_or_else(|| panic!("binary/bits bit field expects heap bitstring"));
                let p = bitstring_like_ptr(bits)
                    .unwrap_or_else(|| panic!("binary/bits bit field expects heap bitstring"));
                if !unsafe { crate::procbin::is_bitstring_like(p) } {
                    panic!("binary/bits bit field source is not a Bitstring");
                }
                let src_bit_len = unsafe { crate::procbin::bitstring_bit_len(p) } as usize;
                let src_bytes_ptr = unsafe { crate::procbin::bitstring_byte_ptr(p) };
                let needed_bits = match (ty, size) {
                    (BitType::Binary, None) => src_bit_len,
                    (BitType::Binary, Some(n)) => (n * unit) as usize,
                    (BitType::Bits, None) => src_bit_len,
                    (BitType::Bits, Some(n)) => (n * unit) as usize,
                    _ => unreachable!(),
                };
                assert!(
                    needed_bits <= src_bit_len,
                    "binary/bits field exceeds source"
                );
                let src_bytes =
                    unsafe { std::slice::from_raw_parts(src_bytes_ptr, src_bit_len.div_ceil(8)) };
                if needed_bits % 8 == 0 && w.bit_len.is_multiple_of(8) {
                    w.bytes.extend_from_slice(&src_bytes[..needed_bits / 8]);
                    w.bit_len += needed_bits;
                } else {
                    let mut r = crate::bitstr::BitReader {
                        bytes: src_bytes,
                        bit_len: src_bit_len,
                        pos: 0,
                    };
                    for _ in 0..needed_bits {
                        w.append_bit(r.read_bit().unwrap());
                    }
                }
            }
            BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => {
                let cp = match value.kind() {
                    ValueKind::INT => value.raw() as u32,
                    _ => panic!("utf field expects integer codepoint"),
                };
                let bytes = match ty {
                    BitType::Utf8 => crate::bitstr::encode_utf8(cp),
                    BitType::Utf16 => crate::bitstr::encode_utf16(cp, endian),
                    BitType::Utf32 => crate::bitstr::encode_utf32(cp, endian),
                    _ => unreachable!(),
                };
                let bytes = bytes.expect("invalid codepoint");
                w.write_bytes(&bytes);
            }
            BitType::Float => {
                use crate::bitstr::apply_endian_for_write;
                let total = size.unwrap_or(64) * unit;
                if total != 32 && total != 64 {
                    panic!("float bit field size must be 32 or 64, got {}", total);
                }
                let f = match value.kind() {
                    ValueKind::FLOAT => f64::from_bits(value.raw()),
                    ValueKind::INT => value.raw() as i64 as f64,
                    _ => panic!("float bit field expects Int or Float"),
                };
                let raw: u64 = if total == 32 {
                    (f as f32).to_bits() as u64
                } else {
                    f.to_bits()
                };
                let raw = apply_endian_for_write(raw, total, endian);
                w.write_bits(raw, total as usize);
            }
        }
    }
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_bs_finalize(process: *mut Process) -> u64 {
    let w = (unsafe { &mut *process })
        .bs_builder
        .take()
        .expect("fz_bs_finalize without fz_bs_begin");
    let bit_len = w.bit_len as u64;
    let bytes = w.bytes;
    let p = (unsafe { &mut *process })
        .heap
        .alloc_bitstring(&bytes, bit_len);
    if bytes.len() > crate::heap::SHARED_BIN_THRESHOLD_BYTES {
        heap_ref_word(ValueKind::PROCBIN, p)
    } else {
        heap_ref_word(ValueKind::BITSTRING, p)
    }
}

/// fz-cty.8 — single-shot bitstring allocation from module-interned bytes.
///
/// Replaces the begin/write-per-field/finalize sequence for the common
/// case of an all-constant byte-literal bitstring (e.g. `<<1, 2, ..., 70>>`).
/// `ptr` points at a static byte payload baked into the module; the runtime
/// copies through `Heap::alloc_bitstring`, which picks inline / ProcBin /
/// SharedBin storage by length.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_alloc_bitstring_const(
    process: *mut Process,
    ptr: u64,
    byte_len: u64,
    bit_len: u64,
) -> u64 {
    // ptr is the address of a module-baked byte payload (Cranelift Local data
    // symbol). It outlives the call; we materialise a slice over it just long
    // enough for Heap::alloc_bitstring to copy / wrap.
    let bytes = unsafe { std::slice::from_raw_parts(ptr as *const u8, byte_len as usize) };
    let p = (unsafe { &mut *process })
        .heap
        .alloc_bitstring(bytes, bit_len);
    if bytes.len() > crate::heap::SHARED_BIN_THRESHOLD_BYTES {
        heap_ref_word(ValueKind::PROCBIN, p)
    } else {
        heap_ref_word(ValueKind::BITSTRING, p)
    }
}

/// fz-q8d.2 — allocate a ProcBin on the current heap referencing a
/// compiler-baked static SharedBin in `.data`. The static SharedBin's
/// refcount anchor (initial value 1) is kept; we retain to climb to 2,
/// then the new ProcBin's lifetime release brings it back to 1 (anchor
/// preserved). The noop destructor never runs in practice.
///
/// `static_sharedbin` is the address of the 40-byte SharedBin struct
/// emitted into `.data` by codegen, with bytes_ptr and destructor
/// relocations resolved by the linker.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_alloc_procbin_from_static(
    process: *mut Process,
    static_sharedbin: u64,
) -> u64 {
    let sb = static_sharedbin as *mut crate::procbin::SharedBin;
    let handle = unsafe { crate::procbin::SharedBinHandle::retain_from_raw(sb) };
    let pb = crate::procbin::alloc_procbin(&mut (unsafe { &mut *process }).heap, handle);
    heap_ref_word(ValueKind::PROCBIN, pb.as_raw() as *const u8)
}

fn decode_bit_type(t: u32) -> crate::bitstr::BitType {
    use crate::bitstr::BitType;
    match t {
        0 => BitType::Integer,
        1 => BitType::Float,
        2 => BitType::Binary,
        3 => BitType::Bits,
        4 => BitType::Utf8,
        5 => BitType::Utf16,
        6 => BitType::Utf32,
        _ => panic!("unknown bit type tag {}", t),
    }
}

fn decode_endian(e: u32) -> crate::bitstr::Endian {
    use crate::bitstr::Endian;
    match e {
        0 => Endian::Big,
        1 => Endian::Little,
        2 => Endian::Native,
        _ => panic!("unknown endian tag {}", e),
    }
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

fn decode_bs_field_spec(spec: u64) -> (u32, u32, u32, u32, u32, u32) {
    (
        ((spec >> BS_FIELD_TY_SHIFT) & BS_FIELD_TY_MASK) as u32,
        ((spec >> BS_FIELD_SIZE_PRESENT_SHIFT) & 1) as u32,
        ((spec >> BS_FIELD_UNIT_SHIFT) & BS_FIELD_UNIT_MASK) as u32,
        ((spec >> BS_FIELD_ENDIAN_SHIFT) & BS_FIELD_ENDIAN_MASK) as u32,
        ((spec >> BS_FIELD_SIGNED_SHIFT) & 1) as u32,
        ((spec >> BS_FIELD_LAST_SHIFT) & 1) as u32,
    )
}

/// Allocate a 3-tuple reader `[bs_ptr, bit_len_int, pos_int]` for an input
/// bitstring. Schema id is set by compile() into BS_TUPLE_ARITY3_SCHEMA.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_bs_reader_init_ref(process: *mut Process, bs_ref: u64) -> u64 {
    fz_bs_reader_init_bits(
        process,
        heap_object_word_from_ref_word(bs_ref, "fz_bs_reader_init_ref"),
    )
}

fn fz_bs_reader_init_bits(process: *mut Process, bs_bits: u64) -> u64 {
    let p = bitstring_like_ptr(bs_bits).unwrap_or_else(|| panic!("reader_init expects heap value"));
    if !unsafe { crate::procbin::is_bitstring_like(p) } {
        panic!("reader_init source is not a Bitstring");
    }
    let bit_len = unsafe { crate::procbin::bitstring_bit_len(p) } as i64;
    let proc = unsafe { &mut *process };
    let arity3 = proc
        .bs_tuple_arity3_schema
        .expect("bs_tuple_arity3_schema not set");
    let tuple_p = proc.heap.alloc_struct(arity3);
    proc.heap
        .write_field_slot(tuple_p, 0, any_value_from_heap_object_word(bs_bits));
    proc.heap
        .write_field_slot(tuple_p, 8, crate::any_value::AnyValue::int(bit_len));
    proc.heap
        .write_field_slot(tuple_p, 16, crate::any_value::AnyValue::int(0));
    heap_ref_word(ValueKind::STRUCT, tuple_p as *const u8)
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_bs_read_field_ref(
    process: *mut Process,
    reader_ref: u64,
    field_spec: u64,
    size_value: u32,
) -> u64 {
    let (ty_tag, size_present, unit, endian_tag, signed, is_last) =
        decode_bs_field_spec(field_spec);
    fz_bs_read_field_bits(
        process,
        heap_object_word_from_ref_word(reader_ref, "fz_bs_read_field_ref"),
        ty_tag,
        size_present,
        size_value,
        unit,
        endian_tag,
        signed,
        is_last,
    )
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_bs_reader_done_ref(process: *mut Process, reader_ref: u64) -> u8 {
    let reader = any_value_ref_from_word(reader_ref, "fz_bs_reader_done_ref")
        .struct_addr()
        .expect("fz_bs_reader_done_ref");
    let bit_len = (unsafe { &mut *process })
        .heap
        .read_field_slot(reader, 8)
        .raw();
    let pos = (unsafe { &mut *process })
        .heap
        .read_field_slot(reader, 16)
        .raw();
    (bit_len == pos) as u8
}

#[allow(clippy::too_many_arguments)]
fn fz_bs_read_field_bits(
    process: *mut Process,
    reader_bits: u64,
    ty_tag: u32,
    size_present: u32,
    size_value: u32,
    unit: u32,
    endian_tag: u32,
    signed: u32,
    is_last: u32,
) -> u64 {
    use crate::bitstr::BitType;
    use crate::bitstr::{apply_endian_for_read, sign_extend};
    let ty = decode_bit_type(ty_tag);
    let size = if size_present != 0 {
        Some(size_value)
    } else {
        None
    };
    let endian = decode_endian(endian_tag);
    let signed_b = signed != 0;
    let is_last_b = is_last != 0;

    // Decode reader tuple.
    let rp = crate::any_value::struct_addr_from_tagged(reader_bits)
        .unwrap_or_else(|| panic!("read_field: reader is not a tagged Struct"));
    let bs_bits = (unsafe { &mut *process })
        .heap
        .read_field_slot(rp, 0)
        .heap_object_word()
        .expect("reader bitstring bits");
    let bit_len = (unsafe { &mut *process }).heap.read_field_slot(rp, 8).raw() as usize;
    let pos = (unsafe { &mut *process })
        .heap
        .read_field_slot(rp, 16)
        .raw() as usize;

    // Bytes pointer from bs.
    let bsp = bitstring_like_ptr(bs_bits).expect("read_field: reader bs not a ptr");
    if !unsafe { crate::procbin::is_bitstring_like(bsp) } {
        panic!("read_field reader bs is not a Bitstring");
    }
    let bytes_ptr = unsafe { crate::procbin::bitstring_byte_ptr(bsp) };
    let bytes = unsafe { std::slice::from_raw_parts(bytes_ptr, bit_len.div_ceil(8)) };

    // Failure path: alloc 1-tuple [false].
    let arity1 = (unsafe { &mut *process })
        .bs_tuple_arity1_schema
        .expect("bs_tuple_arity1_schema not set");
    let arity3 = (unsafe { &mut *process })
        .bs_tuple_arity3_schema
        .expect("bs_tuple_arity3_schema not set");
    let fail = || -> u64 {
        let p = (unsafe { &mut *process }).heap.alloc_struct(arity1);
        (unsafe { &mut *process }).heap.write_field_slot(
            p,
            0,
            crate::any_value::AnyValue::bool_atom(false),
        );
        heap_ref_word(ValueKind::STRUCT, p)
    };

    let mut r = crate::bitstr::BitReader {
        bytes,
        bit_len,
        pos,
    };

    let (extracted_value, consumed) = match ty {
        BitType::Integer => {
            let total = size.unwrap_or(8) * unit;
            if total > 64 {
                return fail();
            }
            let raw = match r.read_bits(total as usize) {
                Some(v) => v,
                None => return fail(),
            };
            let raw = apply_endian_for_read(raw, total, endian);
            let n: i64 = if signed_b {
                sign_extend(raw, total)
            } else {
                raw as i64
            };
            (crate::any_value::AnyValue::int(n), total as usize)
        }
        BitType::Binary | BitType::Bits => {
            let needed_bits = match (ty, size, is_last_b) {
                (BitType::Binary, None, true) | (BitType::Bits, None, true) => bit_len - pos,
                (BitType::Binary, None, false) => return fail(), // size required
                (BitType::Bits, None, false) => return fail(),
                (BitType::Binary, Some(n), _) => (n * unit) as usize,
                (BitType::Bits, Some(n), _) => (n * unit) as usize,
                _ => unreachable!(),
            };
            if pos + needed_bits > bit_len {
                return fail();
            }
            // Build a fresh Bitstring from the slice. Always copy for v1
            // (zero-copy slicing deferred — see ticket "Open").
            let mut sub_bytes = Vec::with_capacity(needed_bits.div_ceil(8));
            let mut w = crate::bitstr::BitWriter::new();
            for _ in 0..needed_bits {
                w.append_bit(r.read_bit().unwrap());
            }
            sub_bytes.extend_from_slice(&w.bytes);
            let new_bs = (unsafe { &mut *process })
                .heap
                .alloc_bitstring(&sub_bytes, needed_bits as u64);
            let new_bs_kind = if sub_bytes.len() > crate::heap::SHARED_BIN_THRESHOLD_BYTES {
                crate::any_value::ValueKind::PROCBIN
            } else {
                crate::any_value::ValueKind::BITSTRING
            };
            (
                crate::any_value::AnyValue::heap_ptr(new_bs, new_bs_kind),
                needed_bits,
            )
        }
        BitType::Float => {
            let total = size.unwrap_or(64) * unit;
            if total != 32 && total != 64 {
                return fail();
            }
            panic!("BitReadField cannot materialize float as one-word ValueRef")
        }
        BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => {
            // UTF: read uses crate::bitstr::decode_utf*; not exercised by
            // ticket tests, so panic to surface intent rather than partial.
            panic!(
                "BitReadField for {:?} not yet wired in JIT (lands with UTF support)",
                ty
            );
        }
    };

    // Allocate fresh reader tuple [bs_bits, bit_len_boxed, new_pos_boxed].
    let new_pos = (pos + consumed) as i64;
    let new_reader_p = (unsafe { &mut *process }).heap.alloc_struct(arity3);
    (unsafe { &mut *process }).heap.write_field_slot(
        new_reader_p,
        0,
        any_value_from_heap_object_word(bs_bits),
    );
    (unsafe { &mut *process }).heap.write_field_slot(
        new_reader_p,
        8,
        crate::any_value::AnyValue::int(bit_len as i64),
    );
    (unsafe { &mut *process }).heap.write_field_slot(
        new_reader_p,
        16,
        crate::any_value::AnyValue::int(new_pos),
    );

    // Allocate result tuple [true, extracted, new_reader].
    let result_p = (unsafe { &mut *process }).heap.alloc_struct(arity3);
    (unsafe { &mut *process }).heap.write_field_slot(
        result_p,
        0,
        crate::any_value::AnyValue::bool_atom(true),
    );
    (unsafe { &mut *process })
        .heap
        .write_field_slot(result_p, 8, extracted_value);
    (unsafe { &mut *process }).heap.write_field_slot(
        result_p,
        16,
        crate::any_value::AnyValue::heap_ptr(new_reader_p, crate::any_value::ValueKind::STRUCT),
    );
    heap_ref_word(ValueKind::STRUCT, result_p as *const u8)
}

// ===== Map cluster (fz-ul4.23.4.8) =====
//
// Maps use a heap-backed sorted-array layout. Construction is immutable:
// start with an empty map, then each put copies the existing entries and
// returns a new map with the key inserted/replaced.
//
// Key total ordering for canonical layout: Int < Atom < Special < Ptr;
// within each category, by raw bits (Int compares signed). Keys compare
// equal iff their u64 bits are equal — pointer-equal heap keys for v1.

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_empty(process: *mut Process) -> u64 {
    map_ref_word_from_bits((unsafe { &mut *process }).heap.alloc_map_slots(&[]))
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_dest_begin(process: *mut Process, extra: u32) -> u64 {
    map_ref_word_from_bits(
        (unsafe { &mut *process })
            .heap
            .alloc_map_destination(None, extra as usize),
    )
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_dest_begin_update(
    process: *mut Process,
    base_ref_word: u64,
    extra: u32,
) -> u64 {
    let base = any_value_ref_from_word(base_ref_word, "fz_map_dest_begin_update base");
    map_ref_word_from_bits(
        (unsafe { &mut *process })
            .heap
            .alloc_map_destination(Some(base), extra as usize),
    )
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_dest_put_parts(
    process: *mut Process,
    dest_ref_word: u64,
    key_raw: u64,
    key_kind: u64,
    value_raw: u64,
    value_kind: u64,
) {
    let dest_bits = map_bits_from_ref_word(dest_ref_word, "fz_map_dest_put_parts dest");
    let key = crate::any_value::AnyValue::decode_parts(key_raw, key_kind as u8)
        .expect("fz_map_dest_put_parts key");
    let value = crate::any_value::AnyValue::decode_parts(value_raw, value_kind as u8)
        .expect("fz_map_dest_put_parts value");
    (unsafe { &mut *process })
        .heap
        .map_destination_put(dest_bits, key, value);
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_dest_put_ref(
    process: *mut Process,
    dest_ref_word: u64,
    key_ref_word: u64,
    value_ref_word: u64,
) {
    let dest_bits = map_bits_from_ref_word(dest_ref_word, "fz_map_dest_put_ref dest");
    let key = any_value_from_ref_word(key_ref_word, "fz_map_dest_put_ref key");
    let value = any_value_from_ref_word(value_ref_word, "fz_map_dest_put_ref value");
    (unsafe { &mut *process })
        .heap
        .map_destination_put(dest_bits, key, value);
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_dest_freeze(process: *mut Process, dest_ref_word: u64) -> u64 {
    let dest_bits = map_bits_from_ref_word(dest_ref_word, "fz_map_dest_freeze dest");
    map_ref_word_from_bits(
        (unsafe { &mut *process })
            .heap
            .map_destination_freeze(dest_bits),
    )
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_get_ref(
    process: *mut Process,
    map_ref_word: u64,
    key_ref_word: u64,
) -> u64 {
    let map = any_value_ref_from_word(map_ref_word, "fz_map_get_ref map");
    let key = any_value_ref_from_word(key_ref_word, "fz_map_get_ref key");
    fz_map_get_value_ref(process, map, key)
}

fn fz_map_get_value_ref(process: *mut Process, map: AnyValueRef, key: AnyValueRef) -> u64 {
    if map.tag() == ValueKind::RESOURCE {
        let rs = unsafe {
            crate::resource::ResourceStub::from_raw(map.resource_addr().expect("resource map get"))
        };
        let _ = key;
        return AnyValueRef::from_scalar_slot(ValueKind::INT, rs.payload_slot())
            .expect("resource integer payload ref")
            .raw_word();
    }
    (unsafe { &mut *process })
        .heap
        .read_map_value_ref(map, key)
        .expect("fz_map_get_ref")
        .unwrap_or_else(|| {
            AnyValueRef::from_scalar_slot(ValueKind::ATOM, &NIL_ATOM_REF_SLOT)
                .expect("static nil atom ref")
        })
        .raw_word()
}

fn fz_map_get_scalar_key_ref(
    process: *mut Process,
    map: AnyValueRef,
    key: crate::any_value::AnyValue,
) -> u64 {
    if map.tag() == ValueKind::RESOURCE {
        let rs = unsafe {
            crate::resource::ResourceStub::from_raw(map.resource_addr().expect("resource map get"))
        };
        let _ = key;
        return AnyValueRef::from_scalar_slot(ValueKind::INT, rs.payload_slot())
            .expect("resource integer payload ref")
            .raw_word();
    }
    (unsafe { &mut *process })
        .heap
        .read_map_value_for_any_key(map, key)
        .expect("fz_map_get scalar key")
        .unwrap_or_else(|| {
            AnyValueRef::from_scalar_slot(ValueKind::ATOM, &NIL_ATOM_REF_SLOT)
                .expect("static nil atom ref")
        })
        .raw_word()
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_get_atom_key_ref(
    process: *mut Process,
    map_ref_word: u64,
    atom_id: u64,
) -> u64 {
    let map = any_value_ref_from_word(map_ref_word, "fz_map_get_atom_key_ref map");
    fz_map_get_scalar_key_ref(
        process,
        map,
        crate::any_value::AnyValue::atom(atom_id as u32),
    )
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_get_int_key_ref(
    process: *mut Process,
    map_ref_word: u64,
    value: i64,
) -> u64 {
    let map = any_value_ref_from_word(map_ref_word, "fz_map_get_int_key_ref map");
    fz_map_get_scalar_key_ref(process, map, crate::any_value::AnyValue::int(value))
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_get_float_key_ref(
    process: *mut Process,
    map_ref_word: u64,
    value: f64,
) -> u64 {
    let map = any_value_ref_from_word(map_ref_word, "fz_map_get_float_key_ref map");
    fz_map_get_scalar_key_ref(process, map, crate::any_value::AnyValue::float(value))
}

fn map_put_slot_value(
    process: *mut Process,
    map_ref_word: u64,
    key: crate::any_value::AnyValue,
    value: crate::any_value::AnyValue,
) -> u64 {
    let map_bits = map_bits_from_ref_word(map_ref_word, "map_put map");
    let new_map_bits = (unsafe { &mut *process })
        .heap
        .map_put_slot_bits(map_bits, key, value);
    map_ref_word_from_bits(new_map_bits)
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_put_ref(
    process: *mut Process,
    map_ref_word: u64,
    key_ref_word: u64,
    value_ref_word: u64,
) -> u64 {
    let key = any_value_ref_from_word(key_ref_word, "fz_map_put_ref key");
    let value = any_value_ref_from_word(value_ref_word, "fz_map_put_ref value");
    if value.tag().is_scalar() {
        panic!(
            "fz_map_put_ref value requires a heap/sentinel ref; use the typed scalar write path"
        );
    }
    map_put_slot_value(
        process,
        map_ref_word,
        crate::any_value::AnyValue::from_ref(key).expect("fz_map_put_ref key"),
        crate::any_value::AnyValue::from_ref(value).expect("fz_map_put_ref value"),
    )
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_put_int(
    process: *mut Process,
    map_ref_word: u64,
    key_ref_word: u64,
    value: i64,
) -> u64 {
    let key = any_value_ref_from_word(key_ref_word, "fz_map_put_int key");
    map_put_slot_value(
        process,
        map_ref_word,
        crate::any_value::AnyValue::from_ref(key).expect("fz_map_put_int key"),
        crate::any_value::AnyValue::int(value),
    )
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_put_float(
    process: *mut Process,
    map_ref_word: u64,
    key_ref_word: u64,
    value: f64,
) -> u64 {
    let key = any_value_ref_from_word(key_ref_word, "fz_map_put_float key");
    map_put_slot_value(
        process,
        map_ref_word,
        crate::any_value::AnyValue::from_ref(key).expect("fz_map_put_float key"),
        crate::any_value::AnyValue::float(value),
    )
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_put_atom(
    process: *mut Process,
    map_ref_word: u64,
    key_ref_word: u64,
    atom_id: u64,
) -> u64 {
    let key = any_value_ref_from_word(key_ref_word, "fz_map_put_atom key");
    map_put_slot_value(
        process,
        map_ref_word,
        crate::any_value::AnyValue::from_ref(key).expect("fz_map_put_atom key"),
        crate::any_value::AnyValue::atom(atom_id as u32),
    )
}

macro_rules! scalar_key_map_put {
    ($name:ident, $key_ty:ty, $value_ty:ty, $key:expr, $value:expr) => {
        #[unsafe(no_mangle)]
        #[allow(clippy::not_unsafe_ptr_arg_deref)]
        pub extern "C" fn $name(
            process: *mut Process,
            map_ref_word: u64,
            key: $key_ty,
            value: $value_ty,
        ) -> u64 {
            map_put_slot_value(process, map_ref_word, $key(key), $value(value))
        }
    };
}

scalar_key_map_put!(
    fz_map_put_atom_key_int,
    u64,
    i64,
    |key| crate::any_value::AnyValue::atom(key as u32),
    crate::any_value::AnyValue::int
);
scalar_key_map_put!(
    fz_map_put_atom_key_float,
    u64,
    f64,
    |key| crate::any_value::AnyValue::atom(key as u32),
    crate::any_value::AnyValue::float
);
scalar_key_map_put!(
    fz_map_put_atom_key_atom,
    u64,
    u64,
    |key| crate::any_value::AnyValue::atom(key as u32),
    |value| crate::any_value::AnyValue::atom(value as u32)
);
scalar_key_map_put!(
    fz_map_put_int_key_int,
    i64,
    i64,
    crate::any_value::AnyValue::int,
    crate::any_value::AnyValue::int
);
scalar_key_map_put!(
    fz_map_put_int_key_float,
    i64,
    f64,
    crate::any_value::AnyValue::int,
    crate::any_value::AnyValue::float
);
scalar_key_map_put!(
    fz_map_put_int_key_atom,
    i64,
    u64,
    crate::any_value::AnyValue::int,
    |value| crate::any_value::AnyValue::atom(value as u32)
);
scalar_key_map_put!(
    fz_map_put_float_key_int,
    f64,
    i64,
    crate::any_value::AnyValue::float,
    crate::any_value::AnyValue::int
);
scalar_key_map_put!(
    fz_map_put_float_key_float,
    f64,
    f64,
    crate::any_value::AnyValue::float,
    crate::any_value::AnyValue::float
);
scalar_key_map_put!(
    fz_map_put_float_key_atom,
    f64,
    u64,
    crate::any_value::AnyValue::float,
    |value| crate::any_value::AnyValue::atom(value as u32)
);

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_get_int(
    process: *mut Process,
    map_ref_word: u64,
    key_ref_word: u64,
) -> i64 {
    map_get_int_impl(process, map_ref_word, key_ref_word)
}

fn map_get_int_impl(process: *mut Process, map_ref_word: u64, key_ref_word: u64) -> i64 {
    ref_load_int_impl(fz_map_get_ref(process, map_ref_word, key_ref_word))
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_get_float(
    process: *mut Process,
    map_ref_word: u64,
    key_ref_word: u64,
) -> f64 {
    ref_load_float_impl(fz_map_get_ref(process, map_ref_word, key_ref_word))
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_map_get_atom(
    process: *mut Process,
    map_ref_word: u64,
    key_ref_word: u64,
) -> u64 {
    ref_load_atom_impl(fz_map_get_ref(process, map_ref_word, key_ref_word))
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_is_map(map_ref_word: u64) -> u8 {
    (any_value_ref_from_word(map_ref_word, "fz_map_is_map").tag() == ValueKind::MAP) as u8
}

// ===== Alloc cluster (fz-ul4.23.4.7) =====

#[unsafe(no_mangle)]
pub extern "C" fn fz_list_is_cons(list_ref_word: u64) -> u8 {
    (any_value_ref_from_word(list_ref_word, "fz_list_is_cons").tag() == ValueKind::LIST) as u8
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_list_cons_ref(
    process: *mut Process,
    head_ref_word: u64,
    tail_ref_word: u64,
) -> u64 {
    let head = any_value_ref_from_word(head_ref_word, "fz_list_cons_ref head");
    let tail = any_value_ref_from_word(tail_ref_word, "fz_list_cons_ref tail");
    (unsafe { &mut *process })
        .heap
        .alloc_list_cons_ref(head, tail)
        .expect("fz_list_cons_ref")
        .raw_word()
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_list_cons_any(
    process: *mut Process,
    head_ref_word: u64,
    tail_ref_word: u64,
) -> u64 {
    let head = any_value_from_ref_word(head_ref_word, "fz_list_cons_any head");
    let tail = any_value_ref_from_word(tail_ref_word, "fz_list_cons_any tail");
    (unsafe { &mut *process })
        .heap
        .alloc_list_cons_any(head, tail)
        .expect("fz_list_cons_any")
        .raw_word()
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_list_cons_int(process: *mut Process, head: i64, tail_ref_word: u64) -> u64 {
    let tail = any_value_ref_from_word(tail_ref_word, "fz_list_cons_int tail");
    (unsafe { &mut *process })
        .heap
        .alloc_list_cons_int(head, tail)
        .expect("fz_list_cons_int")
        .raw_word()
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_list_cons_float(process: *mut Process, head: f64, tail_ref_word: u64) -> u64 {
    let tail = any_value_ref_from_word(tail_ref_word, "fz_list_cons_float tail");
    (unsafe { &mut *process })
        .heap
        .alloc_list_cons_float(head, tail)
        .expect("fz_list_cons_float")
        .raw_word()
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_list_cons_atom(
    process: *mut Process,
    atom_id: u64,
    tail_ref_word: u64,
) -> u64 {
    let tail = any_value_ref_from_word(tail_ref_word, "fz_list_cons_atom tail");
    (unsafe { &mut *process })
        .heap
        .alloc_list_cons_atom(atom_id as u32, tail)
        .expect("fz_list_cons_atom")
        .raw_word()
}

// Reading a list head/tail is a pure dereference of the self-describing list
// pointer — no allocation, no heap state — so these take no process. (The
// `current_process().heap` receiver is vestigial: the read methods take `&self`
// and ignore it; fz-vdt ctx.8 makes them process-free free functions.)
#[unsafe(no_mangle)]
pub extern "C" fn fz_list_head_ref(list_ref_word: u64) -> u64 {
    let list = any_value_ref_from_word(list_ref_word, "fz_list_head_ref");
    crate::heap::list_head_ref(list)
        .expect("fz_list_head_ref")
        .raw_word()
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
    crate::heap::list_tail_ref(list)
        .expect("fz_list_tail_ref")
        .raw_word()
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_mark_published_ref_aliased(process: *mut Process, value_ref_word: u64) -> u64 {
    let value = any_value_ref_from_word(value_ref_word, "fz_mark_published_ref_aliased");
    (unsafe { &mut *process })
        .heap
        .mark_published_ref_aliased(value)
        .expect("fz_mark_published_ref_aliased")
        .raw_word()
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_list_reuse_or_cons_tail_ref(
    process: *mut Process,
    list_ref_word: u64,
    tail_ref_word: u64,
) -> u64 {
    let list = any_value_ref_from_word(list_ref_word, "fz_list_reuse_or_cons_tail_ref list");
    let tail = any_value_ref_from_word(tail_ref_word, "fz_list_reuse_or_cons_tail_ref tail");
    (unsafe { &mut *process })
        .heap
        .reuse_or_alloc_list_cons_tail(list, tail)
        .expect("fz_list_reuse_or_cons_tail_ref")
        .raw_word()
}

/// Allocate a heap-typed Struct. `schema_id` must already be registered in
/// the current Process's heap SchemaRegistry (shared with CompiledModule).
/// Returns a TAG_STRUCT-tagged heap pointer. Caller is
/// responsible for writing field values into payload slots after allocation.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_alloc_struct(process: *mut Process, schema_id: u32) -> u64 {
    let p = (unsafe { &mut *process }).heap.alloc_struct(schema_id);
    heap_ref_word(ValueKind::STRUCT, p)
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_struct_get_field_ref(
    process: *mut Process,
    struct_ref_word: u64,
    field_offset: u32,
) -> u64 {
    let value = any_value_ref_from_word(struct_ref_word, "fz_struct_get_field_ref");
    (unsafe { &mut *process })
        .heap
        .read_struct_field_ref(value, field_offset)
        .expect("fz_struct_get_field_ref")
        .raw_word()
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_struct_set_field_ref(
    process: *mut Process,
    struct_ref_word: u64,
    field_offset: u32,
    value_ref_word: u64,
) {
    let object = any_value_ref_from_word(struct_ref_word, "fz_struct_set_field_ref object");
    let value = any_value_ref_from_word(value_ref_word, "fz_struct_set_field_ref value");
    (unsafe { &mut *process })
        .heap
        .write_struct_field_ref(object, field_offset, value)
        .expect("fz_struct_set_field_ref");
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_struct_set_field_int(
    process: *mut Process,
    struct_ref_word: u64,
    field_offset: u32,
    value: i64,
) {
    let object = any_value_ref_from_word(struct_ref_word, "fz_struct_set_field_int object");
    let obj = object
        .struct_addr()
        .expect("fz_struct_set_field_int object");
    (unsafe { &mut *process }).heap.write_field_slot(
        obj,
        field_offset,
        crate::any_value::AnyValue::int(value),
    );
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_struct_set_field_float(
    process: *mut Process,
    struct_ref_word: u64,
    field_offset: u32,
    value: f64,
) {
    let object = any_value_ref_from_word(struct_ref_word, "fz_struct_set_field_float object");
    let obj = object
        .struct_addr()
        .expect("fz_struct_set_field_float object");
    (unsafe { &mut *process }).heap.write_field_slot(
        obj,
        field_offset,
        crate::any_value::AnyValue::float(value),
    );
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_struct_set_field_atom(
    process: *mut Process,
    struct_ref_word: u64,
    field_offset: u32,
    atom_id: u64,
) {
    let object = any_value_ref_from_word(struct_ref_word, "fz_struct_set_field_atom object");
    let obj = object
        .struct_addr()
        .expect("fz_struct_set_field_atom object");
    (unsafe { &mut *process }).heap.write_field_slot(
        obj,
        field_offset,
        crate::any_value::AnyValue::atom(atom_id as u32),
    );
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_closure_get_capture_ref(closure_ref_word: u64, index: u64) -> u64 {
    if is_lazy_cont_ref(closure_ref_word) {
        return unsafe { lazy_cont_capture_raw(closure_ref_word, index as usize) };
    }
    let value = any_value_ref_from_word(closure_ref_word, "fz_closure_get_capture_ref");
    crate::heap::closure_capture_ref(value, index as usize)
        .expect("fz_closure_get_capture_ref")
        .raw_word()
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_closure_get_capture_i64(closure_ref_word: u64, index: u64) -> i64 {
    if is_lazy_cont_ref(closure_ref_word) {
        return unsafe { lazy_cont_capture_raw(closure_ref_word, index as usize) as i64 };
    }
    let value = any_value_ref_from_word(closure_ref_word, "fz_closure_get_capture_i64");
    let addr = value
        .closure_addr()
        .expect("fz_closure_get_capture_i64 closure");
    match unsafe { crate::any_value::closure_capture_value(addr, index as usize) } {
        crate::any_value::AnyValue::Int(value) => value,
        other => panic!("fz_closure_get_capture_i64 expected int, got {:?}", other),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_closure_get_capture_f64(closure_ref_word: u64, index: u64) -> f64 {
    if is_lazy_cont_ref(closure_ref_word) {
        return f64::from_bits(unsafe { lazy_cont_capture_raw(closure_ref_word, index as usize) });
    }
    let value = any_value_ref_from_word(closure_ref_word, "fz_closure_get_capture_f64");
    let addr = value
        .closure_addr()
        .expect("fz_closure_get_capture_f64 closure");
    match unsafe { crate::any_value::closure_capture_value(addr, index as usize) } {
        crate::any_value::AnyValue::Float(bits) => f64::from_bits(bits),
        other => panic!("fz_closure_get_capture_f64 expected float, got {:?}", other),
    }
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_closure_set_capture_ref(
    process: *mut Process,
    closure_ref_word: u64,
    index: u64,
    value_ref_word: u64,
) {
    let closure = any_value_ref_from_word(closure_ref_word, "fz_closure_set_capture_ref closure");
    let value = any_value_ref_from_word(value_ref_word, "fz_closure_set_capture_ref value");
    (unsafe { &mut *process })
        .heap
        .write_closure_capture_ref(closure, index as usize, value)
        .expect("fz_closure_set_capture_ref");
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_closure_set_capture_i64(
    process: *mut Process,
    closure_ref_word: u64,
    index: u64,
    value: i64,
) {
    let closure = any_value_ref_from_word(closure_ref_word, "fz_closure_set_capture_i64 closure");
    let addr = closure
        .closure_addr()
        .expect("fz_closure_set_capture_i64 closure");
    unsafe {
        (&mut *process).heap.write_closure_capture_value(
            addr,
            index as usize,
            crate::any_value::AnyValue::Int(value),
        )
    };
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_closure_set_capture_f64(
    process: *mut Process,
    closure_ref_word: u64,
    index: u64,
    value: f64,
) {
    let closure = any_value_ref_from_word(closure_ref_word, "fz_closure_set_capture_f64 closure");
    let addr = closure
        .closure_addr()
        .expect("fz_closure_set_capture_f64 closure");
    unsafe {
        (&mut *process).heap.write_closure_capture_value(
            addr,
            index as usize,
            crate::any_value::AnyValue::Float(value.to_bits()),
        )
    };
}

const LAZY_CONT_CODE_OFF: usize = 0;
const LAZY_CONT_SID_OFF: usize = 8;
const LAZY_CONT_COUNT_OFF: usize = 16;
const LAZY_CONT_RAW_OFF: usize = 32;
const LAZY_CONT_KIND_REF: u8 = 0;
const LAZY_CONT_KIND_I64: u8 = 1;
const LAZY_CONT_KIND_F64: u8 = 2;

#[inline]
fn is_lazy_cont_ref(word: u64) -> bool {
    let tag_shift = crate::any_value::AnyValueRefPacking::current().tag_shift();
    (word >> tag_shift) == crate::any_value::TAG_FWD
}

#[inline]
fn lazy_cont_ptr(word: u64) -> *mut u8 {
    (word & crate::any_value::AnyValueRefPacking::current().address_mask()) as *mut u8
}

#[inline]
unsafe fn lazy_cont_count(ptr: *const u8) -> usize {
    unsafe { *(ptr.add(LAZY_CONT_COUNT_OFF) as *const u64) as usize }
}

#[inline]
unsafe fn lazy_cont_kind_base(ptr: *const u8, count: usize) -> *const u8 {
    unsafe { ptr.add(LAZY_CONT_RAW_OFF + count * std::mem::size_of::<u64>()) }
}

#[inline]
unsafe fn lazy_cont_capture_raw(word: u64, index: usize) -> u64 {
    let ptr = lazy_cont_ptr(word);
    unsafe { *(ptr.add(LAZY_CONT_RAW_OFF + index * std::mem::size_of::<u64>()) as *const u64) }
}

/// Materialize a stack-backed lazy continuation descriptor into a normal
/// scheduler-visible closure. Ordinary closure refs are returned unchanged.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_materialize_cont(process: *mut Process, cont_word: u64) -> u64 {
    if !is_lazy_cont_ref(cont_word) {
        return cont_word;
    }
    let ptr = lazy_cont_ptr(cont_word);
    let code = unsafe { *(ptr.add(LAZY_CONT_CODE_OFF) as *const u64) };
    let sid = unsafe { *(ptr.add(LAZY_CONT_SID_OFF) as *const u64) as u32 };
    let count = unsafe { lazy_cont_count(ptr) };
    let bits = (unsafe { &mut *process })
        .heap
        .alloc_closure_slots(sid, count, 0);
    let addr = crate::any_value::closure_addr_from_tagged(bits).expect("materialized cont bits");
    unsafe { std::ptr::write(addr.add(8) as *mut u64, code) };
    let kind_base = unsafe { lazy_cont_kind_base(ptr, count) };
    for i in 0..count {
        let raw = unsafe { lazy_cont_capture_raw(cont_word, i) };
        let kind = unsafe { *kind_base.add(i) };
        match kind {
            LAZY_CONT_KIND_REF => {
                let value = if is_lazy_cont_ref(raw) {
                    fz_materialize_cont(process, raw)
                } else {
                    raw
                };
                let any = any_value_ref_from_word(value, "fz_materialize_cont capture");
                (unsafe { &mut *process })
                    .heap
                    .write_closure_capture_ref(
                        crate::any_value::AnyValueRef::from_raw_word(closure_ref_word_from_bits(
                            bits,
                        ))
                        .expect("materialized closure ref"),
                        i,
                        any,
                    )
                    .expect("materialized closure capture ref");
            }
            LAZY_CONT_KIND_I64 => unsafe {
                (&mut *process).heap.write_closure_capture_value(
                    addr,
                    i,
                    crate::any_value::AnyValue::Int(raw as i64),
                )
            },
            LAZY_CONT_KIND_F64 => unsafe {
                (&mut *process).heap.write_closure_capture_value(
                    addr,
                    i,
                    crate::any_value::AnyValue::Float(raw),
                )
            },
            _ => panic!("fz_materialize_cont: unknown lazy capture kind {}", kind),
        }
    }
    closure_ref_word_from_bits(bits)
}

/// Allocate a frame for fn `fn_id`, looking up its size in the current
/// Process's frame_sizes table populated at make_process() time.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_alloc_frame_dyn(process: *mut Process, fn_id: u32) -> *mut u8 {
    let size = *(unsafe { &mut *process })
        .frame_sizes
        .get(fn_id as usize)
        .unwrap_or_else(|| panic!("frame_sizes has no entry for fn_id {}", fn_id));
    fz_alloc_frame(process, fn_id, size)
}

/// Public wrapper around the internal frame allocator. Used by the
/// Runtime in src/runtime.rs to spawn a task's entry frame and by
/// ir_codegen for the synchronous run path.
pub fn fz_alloc_frame_for_test(schema_id: u32, total_size: u32) -> *mut u8 {
    // Mirror the old try_current_process() behavior: record on the installed
    // process when there is one, otherwise allocate frame-only (null process).
    let process =
        crate::process::try_current_process().map_or(std::ptr::null_mut(), |p| p as *mut Process);
    fz_alloc_frame(process, schema_id, total_size)
}

thread_local! {
    static FRAME_ALLOC_COUNT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Reset the per-thread frame alloc counter. Call before the code under test.
pub fn frame_alloc_count_reset() {
    FRAME_ALLOC_COUNT.with(|c| c.set(0));
}

/// Drain and return the per-thread frame alloc count since last reset.
pub fn frame_alloc_count_take() -> u64 {
    FRAME_ALLOC_COUNT.with(|c| {
        let n = c.get();
        c.set(0);
        n
    })
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_alloc_frame(
    process: *mut Process,
    schema_id: u32,
    total_size: u32,
) -> *mut u8 {
    FRAME_ALLOC_COUNT.with(|c| c.set(c.get() + 1));
    use std::alloc::{Layout, alloc_zeroed};
    // Round size up to a multiple of 16 to keep allocator happy and ensure
    // the resulting block aligns whatever follows.
    let rounded = ((total_size as usize) + 15) & !15;
    let layout = Layout::from_size_align(rounded, 16).expect("bad frame layout");
    // Codegen always passes the pinned Process*; the for-test helper passes
    // null (it allocates a frame outside any process). Skip stats when absent.
    if !process.is_null() {
        unsafe { &mut *process }
            .heap
            .record_external_alloc(crate::heap::HeapAllocKind::Frame, rounded);
    }
    let p = unsafe { alloc_zeroed(layout) };
    if p.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    unsafe {
        std::ptr::write(p as *mut u16, 0);
        std::ptr::write(p.add(2) as *mut u16, 0);
        std::ptr::write(p.add(4) as *mut u32, total_size);
        std::ptr::write(p.add(8) as *mut u32, schema_id);
        std::ptr::write(p.add(12) as *mut u32, 0);
    }
    p
}

// ===== Arith / cmp / eq cluster (fz-ul4.23.4.1) =====

/// Tag-promotion helper for the JIT's mixed-type arithmetic slow path.
/// fz-ul4.27.9: replaced the per-op fz_arith_* / fz_cmp_* helpers — JIT now
/// promotes integer operands here; raw float operands stay in typed lanes.
#[unsafe(no_mangle)]
pub extern "C" fn fz_promote_f64(raw_int: i64) -> f64 {
    raw_int as f64
}

/// f64 remainder (fmod-style: truncated, sign of dividend). Cranelift has no
/// frem opcode, so the JIT's float-mod slow path calls out here.
#[unsafe(no_mangle)]
pub extern "C" fn fz_fmod(a: f64, b: f64) -> f64 {
    a % b
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_value_eq_ref(process: *mut Process, a_ref: u64, b_ref: u64) -> u64 {
    if a_ref == b_ref {
        return 1;
    }
    let a = any_value_from_ref_word(a_ref, "fz_value_eq_ref lhs");
    let b = any_value_from_ref_word(b_ref, "fz_value_eq_ref rhs");
    u64::from(eq_value(process, a, b))
}

fn eq_value(
    process: *mut Process,
    a: crate::any_value::AnyValue,
    b: crate::any_value::AnyValue,
) -> bool {
    use crate::any_value::ValueKind;
    if matches!(a.kind(), ValueKind::BITSTRING | ValueKind::PROCBIN)
        && matches!(b.kind(), ValueKind::BITSTRING | ValueKind::PROCBIN)
    {
        let ap = a.heap_object_word().expect("bitstring lhs heap word") as *mut u8;
        let bp = b.heap_object_word().expect("bitstring rhs heap word") as *mut u8;
        return (unsafe { crate::procbin::is_bitstring_like(ap) })
            && (unsafe { crate::procbin::is_bitstring_like(bp) })
            && eq_bitstring(ap, bp);
    }
    if a.kind() != b.kind() {
        return false;
    }
    if a.raw() == b.raw() {
        return true;
    }
    match a.kind() {
        ValueKind::LIST => {
            if a.raw() == 0 || b.raw() == 0 {
                false
            } else {
                eq_list(process, a.raw() as *mut u8, b.raw() as *mut u8)
            }
        }
        ValueKind::MAP => eq_map(process, a.raw() as *mut u8, b.raw() as *mut u8),
        ValueKind::STRUCT => {
            let a_schema = unsafe { crate::any_value::struct_schema_id(a.raw() as *const u8) };
            let b_schema = unsafe { crate::any_value::struct_schema_id(b.raw() as *const u8) };
            eq_struct(
                process,
                a.raw() as *mut u8,
                b.raw() as *mut u8,
                a_schema,
                b_schema,
            )
        }
        ValueKind::BITSTRING | ValueKind::PROCBIN => unreachable!("handled before kind check"),
        _ => false,
    }
}

fn eq_list(process: *mut Process, ap: *mut u8, bp: *mut u8) -> bool {
    use crate::any_value::ListCons;
    // Walk both chains in lockstep. NIL terminates both at the same step.
    let mut a = ap as *const u8;
    let mut b = bp as *const u8;
    loop {
        let ac = unsafe { &*(a as *const ListCons) };
        let bc = unsafe { &*(b as *const ListCons) };
        if ac.head_kind() != bc.head_kind() {
            return false;
        }
        if !eq_value(process, ac.head_value(), bc.head_value()) {
            return false;
        }
        // Decide each tail: NIL => done; Ptr to List => recurse; else mismatch.
        let at = ac.tail_bits();
        let bt = bc.tail_bits();
        if at == bt {
            return true; // both NIL (same scalar bits) — common terminator
        }
        // If either tail is non-list, the chains diverge.
        let anp = crate::any_value::list_addr_from_tagged(at);
        let bnp = crate::any_value::list_addr_from_tagged(bt);
        let (Some(anp), Some(bnp)) = (anp, bnp) else {
            return false;
        };
        if anp.is_null() || bnp.is_null() {
            return false;
        }
        a = anp as *const u8;
        b = bnp as *const u8;
    }
}

fn eq_struct(
    process: *mut Process,
    ap: *mut u8,
    bp: *mut u8,
    a_schema: u32,
    b_schema: u32,
) -> bool {
    if a_schema != b_schema {
        return false;
    }
    let reg = (unsafe { &mut *process }).heap.schemas_registry();
    let registry = reg.borrow();
    let schema = registry.get(a_schema);
    for field in &schema.fields {
        match field.kind {
            crate::heap::FieldKind::AnyValue => {
                let av = (unsafe { &mut *process })
                    .heap
                    .read_field_slot(ap, field.offset);
                let bv = (unsafe { &mut *process })
                    .heap
                    .read_field_slot(bp, field.offset);
                if !eq_value(process, av, bv) {
                    return false;
                }
            }
            crate::heap::FieldKind::RawF64 | crate::heap::FieldKind::RawI64 => {
                let av = unsafe { std::ptr::read(ap.add(8 + field.offset as usize) as *const u64) };
                let bv = unsafe { std::ptr::read(bp.add(8 + field.offset as usize) as *const u64) };
                if av != bv {
                    return false;
                }
            }
            crate::heap::FieldKind::RawBytes(n) => {
                let av = unsafe {
                    std::slice::from_raw_parts(ap.add(8 + field.offset as usize), n as usize)
                };
                let bv = unsafe {
                    std::slice::from_raw_parts(bp.add(8 + field.offset as usize), n as usize)
                };
                if av != bv {
                    return false;
                }
            }
        }
    }
    true
}

fn eq_bitstring(ap: *mut u8, bp: *mut u8) -> bool {
    unsafe { crate::procbin::bitstring_like_eq(ap, bp) }
}

fn eq_map(process: *mut Process, ap: *mut u8, bp: *mut u8) -> bool {
    let a_count = unsafe { crate::any_value::map_count(ap as *const u8) };
    let b_count = unsafe { crate::any_value::map_count(bp as *const u8) };
    if a_count != b_count {
        return false;
    }
    // Both maps store entries in canonical sort order (.11.13), so a
    // pairwise walk suffices — same key-position implies same key.
    for i in 0..a_count {
        let (ak, av) = unsafe { crate::any_value::map_entry(ap as *const u8, i) };
        let (bk, bv) = unsafe { crate::any_value::map_entry(bp as *const u8, i) };
        if ak.kind() != bk.kind() || av.kind() != bv.kind() {
            return false;
        }
        if !eq_value(process, ak, bk) {
            return false;
        }
        if !eq_value(process, av, bv) {
            return false;
        }
    }
    true
}

// fz-axu.14 (R1) — utf8 runtime support.

/// Returns 1 if the bitstring's bytes are valid UTF-8 AND the
/// bit-length is byte-aligned (multiple of 8). Returns 0 otherwise.
///
/// Bitstrings that aren't byte-aligned cannot be UTF-8 (UTF-8 is a
/// byte-oriented encoding); this function rejects them up front.
///
/// Called by Utf8.valid?/Utf8.from_bytes/Utf8.from_bytes! (S2,
/// fz-axu.13).
///
/// # Safety
/// The caller must pass a tagged heap pointer that points at a
/// bitstring-like heap object (`Bitstring`/`Heapbin`/`ProcBin`/
/// `SharedBin`). Anything else triggers a panic via
/// `bitstring_bit_len`/`bitstring_byte_ptr`.
#[unsafe(no_mangle)]
pub extern "C" fn fz_bitstring_valid_utf8(bs_bits: u64) -> i64 {
    let p = match bitstring_like_ptr_from_ref(bs_bits) {
        Some(p) => p,
        None => return 0,
    };
    if !unsafe { crate::procbin::is_bitstring_like(p) } {
        return 0;
    }
    let bit_len = unsafe { crate::procbin::bitstring_bit_len(p) } as usize;
    if !bit_len.is_multiple_of(8) {
        return 0;
    }
    let byte_len = bit_len / 8;
    let ptr = unsafe { crate::procbin::bitstring_byte_ptr(p) };
    let slice = unsafe { std::slice::from_raw_parts(ptr, byte_len) };
    match std::str::from_utf8(slice) {
        Ok(_) => 1,
        Err(_) => 0,
    }
}

#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_matcher_map_get_ref(
    process: *mut Process,
    map_ref_word: u64,
    key_ref_word: u64,
) -> u64 {
    let map = any_value_ref_from_word(map_ref_word, "fz_matcher_map_get_ref map");
    let key = any_value_ref_from_word(key_ref_word, "fz_matcher_map_get_ref key");
    (unsafe { &mut *process })
        .heap
        .read_map_value_ref(map, key)
        .expect("fz_matcher_map_get_ref")
        .unwrap_or_else(AnyValueRef::null)
        .raw_word()
}

/// fz-puj.45 (X4) — selective-receive matcher comparison against a
/// constant byte literal. Returns 1 if `val_bits` points at a
/// bitstring-like heap value (Bitstring or ProcBin) whose bit-length is
/// `byte_len * 8` and whose bytes equal the slice
/// `bytes_ptr[..byte_len]`. Returns 0 otherwise (including non-bitstring
/// inputs).
///
/// Used by the receive matcher to discharge `Pattern::Binary(utf8)` /
/// `SwitchKey::Utf8Binary` without first materialising the literal as a
/// heap object. `bytes_ptr` references a module-baked `.data` segment
/// emitted by codegen and outlives the call.
///
/// # Safety
/// `bytes_ptr` must be a readable address with at least `byte_len`
/// initialized bytes. `val_bits` is treated as an opaque AnyValue.
#[unsafe(no_mangle)]
pub extern "C" fn fz_matcher_eq_bytes(val_bits: u64, bytes_ptr: u64, byte_len: u64) -> u32 {
    let Some(p) = bitstring_like_ptr_from_ref(val_bits) else {
        return 0;
    };
    if !unsafe { crate::procbin::is_bitstring_like(p) } {
        return 0;
    }
    let want_bits = byte_len * 8;
    let got_bits = unsafe { crate::procbin::bitstring_bit_len(p) };
    if got_bits != want_bits {
        return 0;
    }
    let val_ptr = unsafe { crate::procbin::bitstring_byte_ptr(p) };
    let val_slice = unsafe { std::slice::from_raw_parts(val_ptr, byte_len as usize) };
    let want_slice =
        unsafe { std::slice::from_raw_parts(bytes_ptr as *const u8, byte_len as usize) };
    if val_slice == want_slice { 1 } else { 0 }
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
mod tests {
    use super::*;
    use crate::any_value::{AnyValue, AnyValueRef, ValueKind};
    use crate::heap::SchemaRegistry;
    use crate::procbin::{bitstring_bit_len, bitstring_byte_ptr};
    use crate::process::current_process;
    use crate::process::{CURRENT_PROCESS, CurrentProcessGuard, Process};
    use std::cell::RefCell;
    use std::rc::Rc;

    /// Install a fresh Process for the duration of `f`. Mirrors the
    /// install/clear dance done by aot_shim and the scheduler, but stays
    /// on the test thread.
    fn with_process<R>(f: impl FnOnce() -> R) -> R {
        let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
        let mut proc = Box::new(Process::new(schemas));
        let prev = CURRENT_PROCESS.with(|c| c.replace(proc.as_mut() as *mut Process));
        let r = f();
        CURRENT_PROCESS.with(|c| c.set(prev));
        r
    }

    fn map_int_value_by_atom_name(map_ref_word: u64, name: &str) -> i64 {
        let process = current_process();
        let map_ref = AnyValueRef::from_raw_word(map_ref_word).expect("stats map ref");
        let map_addr = map_ref.map_addr().expect("stats map addr");
        let count = unsafe { crate::any_value::map_count(map_addr as *const u8) };
        for i in 0..count {
            let (key, value) = unsafe { crate::any_value::map_entry(map_addr as *const u8, i) };
            if key.kind() == ValueKind::ATOM
                && process
                    .atom_names
                    .get(key.raw() as usize)
                    .map(String::as_str)
                    == Some(name)
            {
                if let AnyValue::Int(value) = value {
                    return value;
                }
                panic!("stats key {name} was not an integer: {value:?}");
            }
        }
        panic!("stats key {name} not found");
    }

    #[test]
    fn process_heap_alloc_stats_returns_pre_materialization_snapshot() {
        let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
        let mut process = Process::new(schemas);
        let _guard = CurrentProcessGuard::install(&mut process as *mut Process);
        current_process().heap.reset_alloc_stats();
        let _ = current_process()
            .heap
            .alloc_list_cons_slot(AnyValue::int(1), crate::any_value::EMPTY_LIST_BITS);

        let stats_ref = fz_process_heap_alloc_stats(current_process());
        assert_eq!(map_int_value_by_atom_name(stats_ref, "allocs"), 1);
        assert_eq!(map_int_value_by_atom_name(stats_ref, "list_cons_allocs"), 1);
        assert_eq!(map_int_value_by_atom_name(stats_ref, "map_allocs"), 0);
        assert_eq!(map_int_value_by_atom_name(stats_ref, "scheduler_yields"), 0);
        assert_eq!(
            map_int_value_by_atom_name(stats_ref, "interpreter_yields"),
            0
        );
        assert_eq!(
            map_int_value_by_atom_name(stats_ref, "reductions_remaining"),
            crate::process::DEFAULT_REDUCTIONS_PER_QUANTUM as i64
        );
        assert_eq!(
            map_int_value_by_atom_name(stats_ref, "reductions_per_quantum"),
            crate::process::DEFAULT_REDUCTIONS_PER_QUANTUM as i64
        );
        assert_eq!(
            map_int_value_by_atom_name(stats_ref, "reductions_executed"),
            0
        );
        assert_eq!(map_int_value_by_atom_name(stats_ref, "reduction_yields"), 0);
        assert_eq!(
            map_int_value_by_atom_name(stats_ref, "allocation_pressure_yields"),
            0
        );
        assert_eq!(map_int_value_by_atom_name(stats_ref, "yield_reasons"), 0);
        assert_eq!(
            map_int_value_by_atom_name(stats_ref, "max_yield_continuation_bytes"),
            0
        );
        assert_eq!(
            map_int_value_by_atom_name(stats_ref, "min_yield_continuation_margin_before_bytes",),
            0
        );
        assert_eq!(
            map_int_value_by_atom_name(stats_ref, "min_yield_continuation_margin_after_bytes"),
            0
        );

        let after = current_process().heap.alloc_stats_snapshot();
        assert_eq!(after.list_cons.allocs, 1);
        assert_eq!(after.map.allocs, 1);
        assert_eq!(after.total.allocs, 2);
    }

    #[test]
    fn frame_alloc_records_on_installed_process() {
        let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
        let mut process = Process::new(schemas);
        let _guard = CurrentProcessGuard::install(&mut process as *mut Process);
        current_process().heap.reset_alloc_stats();

        let _ = fz_alloc_frame_for_test(7, 17);

        let stats = current_process().heap.alloc_stats_snapshot();
        assert_eq!(stats.frame.allocs, 1);
        assert_eq!(stats.frame.bytes, 32);
        assert_eq!(stats.total.allocs, 1);
        assert_eq!(stats.total.bytes, 32);
    }

    /// fz-axu.14 (R1) — valid UTF-8 byte-aligned bitstring → 1.
    #[test]
    fn fz_bitstring_valid_utf8_accepts_byte_aligned_utf8() {
        with_process(|| {
            let bytes = "héllo".as_bytes();
            let bits = fz_alloc_bitstring_const(
                current_process(),
                bytes.as_ptr() as u64,
                bytes.len() as u64,
                (bytes.len() * 8) as u64,
            );
            assert_eq!(fz_bitstring_valid_utf8(bits), 1);
        });
    }

    #[test]
    fn yield_mid_flight_report_stashes_runnable_closure() {
        with_process(|| {
            let bits = current_process().heap.alloc_closure_slots(0, 0, 0);
            let closure_addr =
                crate::any_value::closure_addr_from_tagged(bits).expect("closure addr");
            let closure_ref = AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure_addr)
                .expect("closure ref")
                .raw_word();
            let ret = fz_yield_mid_flight_report(
                current_process(),
                closure_ref,
                -1,
                crate::process::YIELD_REASON_REDUCTIONS as u32,
            );
            assert_eq!(ret as u64, crate::scheduler_hooks::YIELD_PTR);
            assert_eq!(current_process().runnable_closure, closure_addr);
            assert_eq!(current_process().scheduler_yields, 1);
            assert_eq!(current_process().reductions_remaining, -1);
            assert_eq!(current_process().reduction_yields, 1);
            assert_eq!(
                current_process().yield_reasons,
                crate::process::YIELD_REASON_REDUCTIONS
            );
            assert_eq!(
                current_process().max_yield_continuation_bytes,
                crate::any_value::closure_size_for_count(0) as u64
            );
            assert!(current_process().min_yield_continuation_margin_after_bytes > 0);
        });
    }

    /// Invalid byte sequence → 0.
    #[test]
    fn fz_bitstring_valid_utf8_rejects_bad_bytes() {
        with_process(|| {
            let bytes = [0xffu8, 0xffu8];
            let bits = fz_alloc_bitstring_const(current_process(), bytes.as_ptr() as u64, 2, 16);
            assert_eq!(fz_bitstring_valid_utf8(bits), 0);
        });
    }

    /// Non-byte-aligned bitstring → 0 even if the byte payload would
    /// be valid UTF-8 — UTF-8 is byte-oriented.
    #[test]
    fn fz_bitstring_valid_utf8_rejects_non_byte_aligned() {
        with_process(|| {
            let bytes = [b'h'];
            let bits = fz_alloc_bitstring_const(current_process(), bytes.as_ptr() as u64, 1, 7);
            assert_eq!(fz_bitstring_valid_utf8(bits), 0);
        });
    }

    /// Brand-mint is identity at the bits level.
    #[test]
    fn fz_brand_bitstring_as_utf8_is_identity() {
        assert_eq!(
            fz_brand_bitstring_as_utf8(0x1234_5678_9abc_def0),
            0x1234_5678_9abc_def0
        );
        assert_eq!(fz_brand_bitstring_as_utf8(0), 0);
    }

    #[test]
    fn ref_projection_helpers_load_scalar_payloads() {
        use crate::any_value::AnyValueRef;

        let int_slot = -42_i64 as u64;
        let float_slot = 3.5_f64.to_bits();
        let atom_slot = 17_u64;
        let int_ref = AnyValueRef::from_scalar_slot(ValueKind::INT, &int_slot).expect("int ref");
        let float_ref =
            AnyValueRef::from_scalar_slot(ValueKind::FLOAT, &float_slot).expect("float ref");
        let atom_ref =
            AnyValueRef::from_scalar_slot(ValueKind::ATOM, &atom_slot).expect("atom ref");

        assert_eq!(fz_ref_tag(int_ref.raw_word()), ValueKind::INT.tag());
        assert_eq!(fz_ref_load_int(int_ref.raw_word()), -42);
        assert_eq!(fz_ref_load_float(float_ref.raw_word()), 3.5);
        assert_eq!(fz_ref_load_atom(atom_ref.raw_word()), 17);
    }

    #[test]
    fn map_typed_get_projects_expected_scalar_value() {
        use crate::any_value::AnyValueRef;

        with_process(|| {
            let key_slot = 1u64;
            let key_ref =
                AnyValueRef::from_scalar_slot(ValueKind::ATOM, &key_slot).expect("key ref");
            let map_bits = current_process().heap.alloc_map_slots(&[(
                crate::any_value::AnyValue::atom(1),
                crate::any_value::AnyValue::int(42),
            )]);
            let map_addr = crate::any_value::map_addr_from_tagged(map_bits).expect("map addr");
            let map_ref = AnyValueRef::from_heap_object(ValueKind::MAP, map_addr).expect("map ref");

            assert_eq!(
                map_get_int_impl(current_process(), map_ref.raw_word(), key_ref.raw_word()),
                42
            );
        });
    }

    #[test]
    fn typed_map_put_ffi_round_trips_atom_key_int_value() {
        with_process(|| {
            let key = fz_box_atom_for_any(current_process(), 1);
            let map = fz_map_put_int(current_process(), fz_map_empty(current_process()), key, 42);
            let map_ref = AnyValueRef::from_raw_word(map).expect("map ref");
            let got = fz_map_get_ref(current_process(), map_ref.raw_word(), key);
            assert_eq!(fz_ref_load_int(got), 42);
        });
    }

    #[test]
    #[should_panic(expected = "fz_ref_load_int")]
    fn map_typed_get_panics_on_wrong_scalar_type() {
        use crate::any_value::AnyValueRef;

        with_process(|| {
            let key_slot = 1u64;
            let key_ref =
                AnyValueRef::from_scalar_slot(ValueKind::ATOM, &key_slot).expect("key ref");
            let map_bits = current_process().heap.alloc_map_slots(&[(
                crate::any_value::AnyValue::atom(1),
                crate::any_value::AnyValue::atom(7),
            )]);
            let map_addr = crate::any_value::map_addr_from_tagged(map_bits).expect("map addr");
            let map_ref = AnyValueRef::from_heap_object(ValueKind::MAP, map_addr).expect("map ref");

            let _ = map_get_int_impl(current_process(), map_ref.raw_word(), key_ref.raw_word());
        });
    }

    /// fz-cty.8 — small (<= threshold) payload allocates inline Bitstring.
    #[test]
    fn alloc_bitstring_const_small_payload_is_inline() {
        with_process(|| {
            let bytes: [u8; 3] = [0xaa, 0xbb, 0xcc];
            let ref_word =
                fz_alloc_bitstring_const(current_process(), bytes.as_ptr() as u64, 3, 24);
            let bitstring_ref = AnyValueRef::from_raw_word(ref_word).expect("bitstring ref");
            let addr = bitstring_ref.bitstring_addr().expect("bitstring addr");
            let bits =
                crate::any_value::heap_object_word(addr, crate::any_value::ValueKind::BITSTRING);
            unsafe {
                assert_eq!(
                    bits & crate::any_value::TAG_MASK,
                    crate::any_value::TAG_BITSTRING,
                    "small payload should pick the strict inline Bitstring tag"
                );
                assert_eq!(bitstring_bit_len(bits as *const u8), 24);
                let bp = bitstring_byte_ptr(bits as *const u8);
                assert_eq!(std::slice::from_raw_parts(bp, 3), &bytes);
            }
        });
    }

    /// fz-q8d.2 — `fz_alloc_procbin_from_static` retains the static
    /// SharedBin's anchor (climbing 1 → 2), allocates a ProcBin that
    /// owns the new edge, and returns it as a tagged ProcBin pointer. When
    /// the holding heap drops, the anchor is preserved (refcount stays
    /// at 1) — the static SharedBin lives forever.
    #[test]
    #[serial_test::serial]
    fn alloc_procbin_from_static_preserves_anchor() {
        use crate::procbin::SharedBin;
        use crate::sync::{AtomicUsize, Ordering};
        // Construct a "static" SharedBin by hand. Its destructor is a
        // noop pointer so the test owns its lifetime explicitly.
        static PAYLOAD: [u8; 8] = [0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe];
        unsafe extern "C" fn noop(_: *mut SharedBin) {}
        let mut sb = SharedBin {
            refcount: AtomicUsize::new(1),
            bit_len: 64,
            bytes_ptr: PAYLOAD.as_ptr(),
            bytes_len: PAYLOAD.len(),
            destructor: noop,
        };
        let sb_ptr = &mut sb as *mut SharedBin;
        with_process(|| {
            let ref_word = fz_alloc_procbin_from_static(current_process(), sb_ptr as u64);
            let procbin_ref = AnyValueRef::from_raw_word(ref_word).expect("procbin ref");
            let addr = procbin_ref.procbin_addr().expect("procbin addr");
            let bits =
                crate::any_value::heap_object_word(addr, crate::any_value::ValueKind::PROCBIN);
            unsafe {
                assert_eq!(
                    bits & crate::any_value::TAG_MASK,
                    crate::any_value::TAG_PROCBIN
                );
                assert_eq!(crate::any_value::object_size(bits), 16);
                assert_eq!(bitstring_bit_len(bits as *const u8), 64);
                let bp = bitstring_byte_ptr(bits as *const u8);
                assert_eq!(std::slice::from_raw_parts(bp, 8), &PAYLOAD[..]);
                // retain climbed anchor 1 -> 2.
                assert_eq!(sb.refcount.load(Ordering::Relaxed), 2);
            }
            // When the with_process drops the temp Process, the heap drop
            // releases the ProcBin's edge, returning refcount to the
            // anchor value 1.
        });
        assert_eq!(sb.refcount.load(Ordering::Relaxed), 1, "anchor preserved");
    }

    /// fz-cty.8 — large (> threshold) payload routes through ProcBin / SharedBin.
    #[test]
    #[serial_test::serial]
    fn alloc_bitstring_const_large_payload_is_procbin() {
        with_process(|| {
            let payload: Vec<u8> = (0..70u8).collect(); // 70 > SHARED_BIN_THRESHOLD_BYTES (64)
            let ref_word = fz_alloc_bitstring_const(
                current_process(),
                payload.as_ptr() as u64,
                payload.len() as u64,
                70 * 8,
            );
            let procbin_ref = AnyValueRef::from_raw_word(ref_word).expect("procbin ref");
            let addr = procbin_ref.procbin_addr().expect("procbin addr");
            let bits =
                crate::any_value::heap_object_word(addr, crate::any_value::ValueKind::PROCBIN);
            unsafe {
                assert_eq!(
                    bits & crate::any_value::TAG_MASK,
                    crate::any_value::TAG_PROCBIN
                );
                assert_eq!(crate::any_value::object_size(bits), 16);
                assert_eq!(bitstring_bit_len(bits as *const u8), 70 * 8);
                let bp = bitstring_byte_ptr(bits as *const u8);
                assert_eq!(
                    std::slice::from_raw_parts(bp, payload.len()),
                    payload.as_slice()
                );
            }
        });
    }
}
