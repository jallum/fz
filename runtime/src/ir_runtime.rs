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
//!   .13 halt/print (fz_halt, fz_print_value)
//!
//! All fns here have unstable `extern "C"` ABI — they're called by
//! Cranelift-emitted code via the symbol-binding list in
//! `ir_codegen::compile`. Do not reorder args or change return types
//! without updating the matching `declare_function` signatures.

use crate::process::current_process;
use crate::tagged_value_ref::TaggedValueRef;

fn value_slot_from_tagged_heap_bits(bits: u64) -> crate::fz_value::ValueSlot {
    crate::fz_value::ValueSlot::decode_tagged_heap_bits(bits)
        .unwrap_or_else(|| panic!("expected strict tagged heap value, got {bits:#x}"))
}

fn tagged_ref_from_word(word: u64, context: &str) -> TaggedValueRef {
    TaggedValueRef::from_raw_word(word)
        .unwrap_or_else(|err| panic!("{context}: invalid tagged value ref {word:#x}: {err:?}"))
}

// ===== Halt + print cluster (fz-ul4.23.4.13) =====

#[unsafe(no_mangle)]
pub extern "C" fn fz_print_value_typed(raw: u64, kind: u8) {
    let value = crate::fz_value::ValueSlot::decode_parts(raw, kind).expect("print value kind");
    crate::emit_print_line(crate::fz_value::debug::render_value(value));
}

thread_local! {
    /// Test-only capture of every fz_print_value rendering. Tests in the
    /// fz binary (ir_codegen::tests) read it via `test_capture_take()`.
    /// Lifted from ir_codegen.rs alongside the FFI body in fz-ul4.23.10.
    pub static TEST_CAPTURE: std::cell::RefCell<Vec<String>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

pub fn test_capture_take() -> Vec<String> {
    TEST_CAPTURE.with(|c| std::mem::take(&mut *c.borrow_mut()))
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_dynamic_float_arith_unsupported() -> u64 {
    panic!("dynamic float arithmetic needs a typed float result carrier")
}

/// fz-ul4.27.22.3 — typed halt for narrow-int seams. The cont chain
/// carries a raw i64 all the way to halt-cont's RawInt body; no
/// unboxing — value is already a machine int.
#[unsafe(no_mangle)]
pub extern "C" fn fz_halt_implicit_i64(val: i64) {
    current_process().halt_value = val;
}

/// fz-ul4.27.22.3 — typed halt for narrow-float seams. Mirrors
/// fz_halt's Boxed-float branch: store `to_bits() as i64` so tests
/// can round-trip via f64::from_bits.
#[unsafe(no_mangle)]
pub extern "C" fn fz_halt_implicit_f64(val: f64) {
    current_process().halt_value = val.to_bits() as i64;
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_halt_implicit_typed(raw: u64, kind: u8) {
    let value = crate::fz_value::ValueSlot::decode_parts(raw, kind).expect("halt value kind");
    current_process().halt_value = halt_value_from_slot(value);
}

fn halt_value_from_slot(value: crate::fz_value::ValueSlot) -> i64 {
    use crate::fz_value::ValueKind;
    match value.kind() {
        ValueKind::INT => value.raw() as i64,
        ValueKind::ATOM => value.raw() as i64,
        ValueKind::FLOAT => value.raw() as i64,
        ValueKind::NULL => 0,
        kind if kind.is_heap() => value.tagged_heap_bits().unwrap_or(value.raw()) as i64,
        _ => value.raw() as i64,
    }
}

// ===== Concurrency cluster (fz-ul4.23.4.12) =====

/// fz-ul4.19.2: scheduler-bound builtins.
///
/// Both consume a Runtime installed in TLS by Runtime::run_until_idle.
/// Calling either outside the scheduler path panics with a clear message.
///
#[unsafe(no_mangle)]
pub extern "C" fn fz_spawn_typed(closure_raw: u64, closure_kind: u8) -> u64 {
    let closure = value_slot_from_parts(closure_raw, closure_kind);
    let closure_bits = closure
        .tagged_heap_bits()
        .expect("spawn: closure not a heap value");
    crate::fz_value::closure_addr_from_tagged(closure_bits).expect("spawn: closure not a closure");
    crate::scheduler_hooks::dispatch_spawn(closure_bits) as u64
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_spawn_opt_typed(
    closure_raw: u64,
    closure_kind: u8,
    min_heap_size: u64,
) -> u64 {
    let closure = value_slot_from_parts(closure_raw, closure_kind);
    let closure_bits = closure
        .tagged_heap_bits()
        .expect("spawn_opt: closure not a heap value");
    crate::fz_value::closure_addr_from_tagged(closure_bits)
        .expect("spawn_opt: closure not a closure");
    crate::scheduler_hooks::dispatch_spawn_opt(closure_bits, min_heap_size as u32) as u64
}

/// fz-swt.10 — `make_resource(payload, dtor)` runtime BIF, callable from
/// the JIT/AOT path. `payload_raw` plus `payload_kind` is the canonical
/// value handed back to the user-supplied dtor; `dtor_closure_bits` is the
/// tagged closure pointer produced by the `&name/arity` form. Returns the
/// tagged `TAG_RESOURCE` stub on the current process heap.
///
/// Dtor resolution requires walking the closure body's IR to find the
/// underlying `Prim::Extern`, so we delegate to the binary-side hook
/// (the runtime crate has no IR Module). The same hook is installed for
/// both interp and JIT/AOT execution — the symbol path is therefore
/// uniform across all three legs (see fz-swt.10's `MakeResourceHook`).
#[unsafe(no_mangle)]
pub extern "C" fn fz_make_resource_typed(
    payload_raw: u64,
    payload_kind: u8,
    dtor_raw: u64,
    dtor_kind: u8,
) -> u64 {
    crate::scheduler_hooks::dispatch_make_resource(payload_raw, payload_kind, dtor_raw, dtor_kind)
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_self_raw() -> u64 {
    current_process().pid as u64
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

/// fz_send_typed(receiver_pid, msg_raw, msg_kind) -> msg_raw.
///
/// Deep-copies msg into the receiver's heap, enqueues into receiver's
/// mailbox, transitions receiver from Blocked to Ready (and re-enqueues)
/// if it was waiting.
///
/// v1 limitations:
/// - Receiver must be a task currently in the Runtime's task registry
///   (panics otherwise).
/// - Message values cross this boundary as explicit strict parts; mailbox
///   storage keeps the same raw+kind shape.
#[unsafe(no_mangle)]
pub extern "C" fn fz_send_typed(receiver_pid_bits: u64, msg_value: u64, msg_kind: u8) -> u64 {
    let receiver_pid = receiver_pid_bits as u32;
    let msg = crate::fz_value::ValueSlot::decode_parts(msg_value, msg_kind)
        .expect("send: invalid message kind");
    let slot = crate::fz_value::OldMailboxSlot::from_value(msg);
    crate::scheduler_hooks::dispatch_send(receiver_pid, slot.value, slot.kind);
    msg.raw()
}

/// fz_receive_attempt(cont_frame_ptr) -> next_frame_ptr.
///
/// If the current Process has a pending message: pop it, deep-copy is NOT
/// needed (message is already in this process's heap — send copied it on
/// arrival), write the msg bits into cont_frame[24] (the cont's first
/// param), return cont_frame_ptr so the trampoline dispatches it.
///
/// If the mailbox is empty: set the Process state to Blocked, return
/// YIELD_PTR. The trampoline parks the task at the receive's frame; on
/// resume (via send), this fn is called again and now finds the message.
/// fz-cps.1.2 — `Term::Receive` cutover entry per docs/cps-in-clif.md §4.
/// Caller has already built the cont closure (with outer_cont at +24,
/// user captures from +32, and code_ptr at +16). This fn stashes the
/// closure in `Process::parked_cont`, sets state Blocked, and returns
/// the YIELD sentinel so the trampoline parks the task.
///
/// On message arrival the scheduler dispatches the parked_cont via the
/// Cranelift-emitted `fz_resume_park` thunk (load parked_cont+16;
/// call_indirect (msg, parked_cont)). The msg is the cont's first
/// param (Tagged ValueSlot); `self` is the cont closure ptr itself.
#[unsafe(no_mangle)]
pub extern "C" fn fz_receive_park(cont_closure_bits: u64) -> *mut u8 {
    use crate::{process::ProcessState, scheduler_hooks::YIELD_PTR};
    let p = current_process();
    p.parked_cont = cont_closure_bits as *mut u8;
    // fz-cps.1.12 — if a message is already waiting (typically from a
    // self-send earlier in the same task), mark the task Ready instead
    // of Blocked so the scheduler re-enqueues it for immediate wakeup
    // through fz_resume_park. Without this, self-send + receive deadlocks
    // (no other task will arrive to flip Blocked→Ready).
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
/// - `pinned_ptr` / `n_pinned`: array of `u64` pinned matcher
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
    matcher_fn_bits: u64,
    pinned_ptr: *const u64,
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
    let pinned: Vec<u64> = if n_pinned == 0 {
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
                .map(|b| *b as *mut u8)
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

    let p = current_process();
    let after_timer_id = match after_deadline_ms {
        Some(after_ms) => crate::scheduler_hooks::dispatch_timer_schedule(p.pid, after_ms),
        None => None,
    };

    let park = ParkRecord {
        matcher_fn,
        pinned,
        clause_bodies,
        clause_bound_counts,
        bound_arity: bound_arity as u16,
        after_deadline_ms,
        after_cont: after_cont_bits as *mut u8,
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

/// # Safety
/// `cont_frame_ptr` must point at a valid cont closure heap object
/// (built by codegen at the Receive seam). Called only from JIT/AOT-
/// emitted Cranelift code; clippy's `not_unsafe_ptr_arg_deref` is
/// silenced because the C ABI is fixed by codegen.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_receive_attempt(cont_frame_ptr: *mut u8) -> *mut u8 {
    use crate::{process::ProcessState, scheduler_hooks::YIELD_PTR};
    let p = current_process();
    if let Some(msg) = p.mailbox.pop_front() {
        let value = msg.value();
        unsafe {
            crate::fz_value::closure_capture_set(cont_frame_ptr as *const u8, 1, value);
        }
        cont_frame_ptr
    } else {
        p.state = ProcessState::Blocked;
        YIELD_PTR as *mut u8
    }
}

// ===== Mid-flight GC helpers (fz-02r.3) =====
//
// Called at back-edge TailCall sites when FZ_SHOULD_YIELD is set. The JIT
// emits a 3-instruction inline check (load FZ_SHOULD_YIELD; cmp 0; jz skip)
// then calls fz_yield_back_edge if the flag is set. The function stashes the
// live args into Process::mid_flight_roots, sets state=Running (yield-style),
// and returns YIELD_PTR so the trampoline breaks out of the quantum loop.
// The scheduler then calls gc_mid_flight, resets the flag, and re-enqueues.

/// Return a raw pointer to the start of `Process::mid_flight_roots`.
/// The JIT uses this to write live args directly into the slab before
/// calling fz_yield_back_edge. Avoids a second pass through the root count.
#[unsafe(no_mangle)]
pub extern "C" fn fz_mid_flight_roots_ptr() -> *mut u64 {
    let p = current_process();
    p.mid_flight_roots.as_mut_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_mid_flight_root_tags_ptr() -> *mut u8 {
    let p = current_process();
    p.mid_flight_root_tags.as_mut_ptr()
}

/// Signal a cooperative back-edge yield. Called by JIT after writing
/// `arg_count` live args into `mid_flight_roots` (via fz_mid_flight_roots_ptr).
/// Stores the callee's raw code pointer (`fn_ptr`) so the scheduler can
/// resume without a spec_id→ptr lookup. Returns YIELD_PTR to break the
/// quantum loop.
#[unsafe(no_mangle)]
pub extern "C" fn fz_yield_back_edge(fn_ptr: u64, arg_count: u32) -> *mut u8 {
    use crate::scheduler_hooks::YIELD_PTR;
    let p = current_process();
    p.mid_flight_fn_ptr = fn_ptr;
    p.mid_flight_root_count = arg_count as u8;
    YIELD_PTR as *mut u8
}

// ===== Closure cluster (fz-ul4.23.4.11) =====
//
// fz-ul4.29.5: closures are (stub_fp, captures...) pairs. Every closure
// invocation is a call_indirect through stub_fp inlined at the call site;
// MakeClosure inlines heap-alloc + stub_fp store + capture writes. The
// only runtime helper left in the closure cluster is the allocator below.

/// Allocate a closure heap object with `captured_count` capture slots.
/// Caller writes fn_ptr at offset 8 and captures at offset 16+.
/// `halt_kind` (fz-ul4.27.22.6) is packed into the closure header's
/// `flags` so `fz_spawn_entry` and `fz_resume_park` can pick the matching
/// halt-cont singleton at task launch.
#[unsafe(no_mangle)]
pub extern "C" fn fz_alloc_closure(callee_fn_id: u32, captured_count: u32, halt_kind: u32) -> u64 {
    FRAME_ALLOC_COUNT.with(|c| c.set(c.get() + 1));
    current_process().heap.alloc_closure_slots(
        callee_fn_id,
        captured_count as usize,
        halt_kind as u16,
    )
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
pub extern "C" fn fz_get_halt_cont(halt_cont_body_addr: u64, kind: u32) -> u64 {
    // fz-ul4.27.22.3 — `kind` selects which of three per-Process halt-cont
    // singletons to return (0=Tagged, 1=RawInt, 2=RawF64). Each holds a
    // body whose Tail-CC sig matches its repr. Producer's Term::Return
    // uses sig (return_repr, i64); the body at +16 must agree.
    let p = current_process();
    let slot = kind as usize;
    if !p.halt_cont_singletons[slot].is_null() {
        return p.halt_cont_singletons[slot] as u64;
    }
    let mut buf = crate::process::AlignedClosureStorage::zeroed();
    let base = buf.as_ptr();
    unsafe {
        std::ptr::write(base as *mut u32, 0);
        std::ptr::write(
            base.add(4) as *mut u32,
            crate::fz_value::closure_flags_pack(0, kind as u16) as u32,
        );
        std::ptr::write(base.add(8) as *mut u64, halt_cont_body_addr);
    }
    p.halt_cont_singletons[slot] =
        crate::fz_value::tagged_closure_bits(base as *const u8) as *mut u8;
    p.static_closure_bufs.push(buf);
    p.halt_cont_singletons[slot] as u64
}

/// fz-cps.1.7 — return the per-Process static zero-capture singleton for
/// the given closure spec id. Populated at `make_process` time from
/// `CompiledModule::static_closure_targets`. Cheaper than
/// `fz_alloc_closure(fid, 0)` + stub_fp store at every `Prim::MakeClosure(fid, [])`
/// site. See docs/cps-in-clif.md §8.2 acceptance: "Module-init region produces
/// double/neg static closures exactly once."
#[unsafe(no_mangle)]
pub extern "C" fn fz_get_static_closure(cl_sid: u32) -> u64 {
    let p = current_process();
    let idx = cl_sid as usize;
    if idx < p.static_closures.len() {
        let ptr = p.static_closures[idx];
        if !ptr.is_null() {
            return ptr as u64;
        }
    }
    // fz-cps.1.12 — fallback search: cl_sid may refer to a narrow spec
    // whose any-key was dropped (typer skipped the bare any-key after
    // .29.12.6), while the singleton was registered under a different
    // narrow sid for the same fn. Match by `_reserved` (fn_id) in the
    // strict closure prefix. Linear in static_closures.len() — small (one entry
    // per zero-cap closure-target spec).
    for ptr in &p.static_closures {
        if ptr.is_null() {
            continue;
        }
        let Some(addr) = crate::fz_value::closure_addr_from_tagged(*ptr as u64) else {
            continue;
        };
        if unsafe { crate::fz_value::closure_schema_id(addr as *const u8) } == cl_sid {
            return *ptr as u64;
        }
    }
    panic!(
        "fz_get_static_closure: no singleton for cl_sid/fn_id {} ({} entries)",
        cl_sid,
        p.static_closures.len()
    );
}

// ===== Bitstring cluster (fz-ul4.23.4.9) =====

fn bitstring_like_ptr(bits: u64) -> Option<*mut u8> {
    if matches!(
        bits & crate::fz_value::TAG_MASK,
        crate::fz_value::TAG_BITSTRING | crate::fz_value::TAG_PROCBIN
    ) {
        Some(bits as *mut u8)
    } else {
        None
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_bs_begin() {
    current_process().bs_builder = Some(crate::bitstr::BitWriter::new());
}

/// Write one field into the active builder. Field-type tags match the order
/// in `crate::bitstr::BitType`: Integer=0, Float=1, Binary=2, Bits=3, Utf8=4,
/// Utf16=5, Utf32=6. `size_present` distinguishes None (0) vs Some (1);
/// `size_value` is in size-units (multiplied by `unit` internally).
#[allow(clippy::too_many_arguments)]
#[unsafe(no_mangle)]
pub extern "C" fn fz_bs_write_field_typed(
    value_raw: u64,
    value_kind: u8,
    ty_tag: u32,
    size_present: u32,
    size_value: u32,
    unit: u32,
    endian_tag: u32,
    signed: u32,
) {
    let value = value_slot_from_parts(value_raw, value_kind);
    fz_bs_write_field_value(
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
    value: crate::fz_value::ValueSlot,
    ty_tag: u32,
    size_present: u32,
    size_value: u32,
    unit: u32,
    endian_tag: u32,
    signed: u32,
) {
    use crate::bitstr::BitType;
    use crate::fz_value::ValueKind;
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
        let w = current_process()
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
                    .tagged_heap_bits()
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
pub extern "C" fn fz_bs_finalize() -> u64 {
    let w = current_process()
        .bs_builder
        .take()
        .expect("fz_bs_finalize without fz_bs_begin");
    let bit_len = w.bit_len as u64;
    let bytes = w.bytes;
    let p = current_process().heap.alloc_bitstring(&bytes, bit_len);
    if bytes.len() > crate::heap::SHARED_BIN_THRESHOLD_BYTES {
        crate::fz_value::tagged_procbin_bits(p)
    } else {
        crate::fz_value::tagged_bitstring_bits(p)
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
pub extern "C" fn fz_alloc_bitstring_const(ptr: u64, byte_len: u64, bit_len: u64) -> u64 {
    // ptr is the address of a module-baked byte payload (Cranelift Local data
    // symbol). It outlives the call; we materialise a slice over it just long
    // enough for Heap::alloc_bitstring to copy / wrap.
    let bytes = unsafe { std::slice::from_raw_parts(ptr as *const u8, byte_len as usize) };
    let p = current_process().heap.alloc_bitstring(bytes, bit_len);
    if bytes.len() > crate::heap::SHARED_BIN_THRESHOLD_BYTES {
        crate::fz_value::tagged_procbin_bits(p)
    } else {
        crate::fz_value::tagged_bitstring_bits(p)
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
pub extern "C" fn fz_alloc_procbin_from_static(static_sharedbin: u64) -> u64 {
    let sb = static_sharedbin as *mut crate::procbin::SharedBin;
    let handle = unsafe { crate::procbin::SharedBinHandle::retain_from_raw(sb) };
    let pb = crate::procbin::alloc_procbin(&mut current_process().heap, handle);
    crate::fz_value::tagged_procbin_bits(pb.as_raw() as *const u8)
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

/// Allocate a 3-tuple reader `[bs_ptr, bit_len_int, pos_int]` for an input
/// bitstring. Schema id is set by compile() into BS_TUPLE_ARITY3_SCHEMA.
#[unsafe(no_mangle)]
pub extern "C" fn fz_bs_reader_init_typed(bs_raw: u64, bs_kind: u8) -> u64 {
    let value = value_slot_from_parts(bs_raw, bs_kind);
    let bs_bits = value
        .tagged_heap_bits()
        .unwrap_or_else(|| panic!("reader_init expects heap value"));
    fz_bs_reader_init_bits(bs_bits)
}

fn fz_bs_reader_init_bits(bs_bits: u64) -> u64 {
    let p = bitstring_like_ptr(bs_bits).unwrap_or_else(|| panic!("reader_init expects heap value"));
    if !unsafe { crate::procbin::is_bitstring_like(p) } {
        panic!("reader_init source is not a Bitstring");
    }
    let bit_len = unsafe { crate::procbin::bitstring_bit_len(p) } as i64;
    let arity3 = current_process()
        .bs_tuple_arity3_schema
        .expect("bs_tuple_arity3_schema not set");
    let tuple_p = current_process().heap.alloc_struct(arity3);
    current_process()
        .heap
        .write_field_slot(tuple_p, 0, value_slot_from_tagged_heap_bits(bs_bits));
    current_process()
        .heap
        .write_field_slot(tuple_p, 8, crate::fz_value::ValueSlot::int(bit_len));
    current_process()
        .heap
        .write_field_slot(tuple_p, 16, crate::fz_value::ValueSlot::int(0));
    crate::fz_value::tagged_struct_bits(tuple_p as *const u8)
}

#[allow(clippy::too_many_arguments)]
#[unsafe(no_mangle)]
pub extern "C" fn fz_bs_read_field_typed(
    reader_raw: u64,
    reader_kind: u8,
    ty_tag: u32,
    size_present: u32,
    size_value: u32,
    unit: u32,
    endian_tag: u32,
    signed: u32,
    is_last: u32,
) -> u64 {
    let value = value_slot_from_parts(reader_raw, reader_kind);
    let reader_bits = value
        .tagged_heap_bits()
        .unwrap_or_else(|| panic!("read_field reader expects heap value"));
    fz_bs_read_field_bits(
        reader_bits,
        ty_tag,
        size_present,
        size_value,
        unit,
        endian_tag,
        signed,
        is_last,
    )
}

#[allow(clippy::too_many_arguments)]
fn fz_bs_read_field_bits(
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
    let rp = crate::fz_value::struct_addr_from_tagged(reader_bits)
        .unwrap_or_else(|| panic!("read_field: reader is not a tagged Struct"));
    let bs_bits = current_process()
        .heap
        .read_field_slot(rp, 0)
        .tagged_heap_bits()
        .expect("reader bitstring bits");
    let bit_len = current_process().heap.read_field_slot(rp, 8).raw() as usize;
    let pos = current_process().heap.read_field_slot(rp, 16).raw() as usize;

    // Bytes pointer from bs.
    let bsp = bitstring_like_ptr(bs_bits).expect("read_field: reader bs not a ptr");
    if !unsafe { crate::procbin::is_bitstring_like(bsp) } {
        panic!("read_field reader bs is not a Bitstring");
    }
    let bytes_ptr = unsafe { crate::procbin::bitstring_byte_ptr(bsp) };
    let bytes = unsafe { std::slice::from_raw_parts(bytes_ptr, bit_len.div_ceil(8)) };

    // Failure path: alloc 1-tuple [false].
    let arity1 = current_process()
        .bs_tuple_arity1_schema
        .expect("bs_tuple_arity1_schema not set");
    let arity3 = current_process()
        .bs_tuple_arity3_schema
        .expect("bs_tuple_arity3_schema not set");
    let fail = || -> u64 {
        let p = current_process().heap.alloc_struct(arity1);
        current_process()
            .heap
            .write_field_slot(p, 0, crate::fz_value::ValueSlot::bool_atom(false));
        crate::fz_value::tagged_struct_bits(p)
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
            (crate::fz_value::ValueSlot::int(n), total as usize)
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
            let new_bs = current_process()
                .heap
                .alloc_bitstring(&sub_bytes, needed_bits as u64);
            let new_bs_kind = if sub_bytes.len() > crate::heap::SHARED_BIN_THRESHOLD_BYTES {
                crate::fz_value::ValueKind::PROCBIN
            } else {
                crate::fz_value::ValueKind::BITSTRING
            };
            (
                crate::fz_value::ValueSlot::heap_ptr(new_bs, new_bs_kind),
                needed_bits,
            )
        }
        BitType::Float => {
            let total = size.unwrap_or(64) * unit;
            if total != 32 && total != 64 {
                return fail();
            }
            panic!("BitReadField cannot materialize float as one-word Tagged")
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
    let new_reader_p = current_process().heap.alloc_struct(arity3);
    current_process().heap.write_field_slot(
        new_reader_p,
        0,
        value_slot_from_tagged_heap_bits(bs_bits),
    );
    current_process().heap.write_field_slot(
        new_reader_p,
        8,
        crate::fz_value::ValueSlot::int(bit_len as i64),
    );
    current_process().heap.write_field_slot(
        new_reader_p,
        16,
        crate::fz_value::ValueSlot::int(new_pos),
    );

    // Allocate result tuple [true, extracted, new_reader].
    let result_p = current_process().heap.alloc_struct(arity3);
    current_process().heap.write_field_slot(
        result_p,
        0,
        crate::fz_value::ValueSlot::bool_atom(true),
    );
    current_process()
        .heap
        .write_field_slot(result_p, 8, extracted_value);
    current_process().heap.write_field_slot(
        result_p,
        16,
        crate::fz_value::ValueSlot::heap_ptr(new_reader_p, crate::fz_value::ValueKind::STRUCT),
    );
    crate::fz_value::tagged_struct_bits(result_p as *const u8)
}

// ===== Map cluster (fz-ul4.23.4.8) =====
//
// Maps use a heap-backed sorted-array layout. Build-time semantics: codegen
// emits begin -> push (per pair) -> finalize. MapUpdate emits clone(base) ->
// push (per override) -> finalize. The thread-local builder accumulates
// pairs as `(key_bits, val_bits)`; finalize sorts canonically (later writes
// win on duplicate keys) and allocates one heap Map.
//
// Key total ordering for canonical layout: Int < Atom < Special < Ptr;
// within each category, by raw bits (Int compares signed). Keys compare
// equal iff their u64 bits are equal — pointer-equal heap keys for v1.

fn map_key_category(value: crate::fz_value::ValueSlot) -> u8 {
    use crate::fz_value::ValueKind;
    match value.kind {
        ValueKind::INT => 0,
        ValueKind::ATOM => 1,
        ValueKind::NULL => 2,
        kind if kind.is_heap() => 3,
        ValueKind::FLOAT => 4,
        _ => 5,
    }
}

fn map_key_cmp(a: crate::fz_value::ValueSlot, b: crate::fz_value::ValueSlot) -> std::cmp::Ordering {
    map_key_category(a)
        .cmp(&map_key_category(b))
        .then_with(|| a.kind.tag().cmp(&b.kind.tag()))
        .then_with(|| {
            if a.kind == crate::fz_value::ValueKind::INT {
                (a.raw as i64).cmp(&(b.raw as i64))
            } else {
                a.raw.cmp(&b.raw)
            }
        })
}

fn value_slot_from_parts(value_bits: u64, kind_tag: u8) -> crate::fz_value::ValueSlot {
    crate::fz_value::ValueSlot::decode_parts(value_bits, kind_tag)
        .unwrap_or_else(|| panic!("invalid strict value parts raw={value_bits:#x} kind={kind_tag}"))
}

fn current_heap_addr_for_kind(bits: u64, kind: crate::fz_value::ValueKind) -> Option<*mut u8> {
    current_process()
        .heap
        .current_heap_addr_for_kind(bits, kind)
}

fn current_heap_map_addr(bits: u64) -> Option<*mut u8> {
    current_heap_addr_for_kind(bits, crate::fz_value::ValueKind::MAP)
}

fn current_heap_list_addr(bits: u64) -> Option<*mut u8> {
    current_heap_addr_for_kind(bits, crate::fz_value::ValueKind::LIST)
}

fn current_heap_resource_addr(bits: u64) -> Option<*mut u8> {
    current_heap_addr_for_kind(bits, crate::fz_value::ValueKind::RESOURCE)
}

fn map_entry_by_value_key(
    p: *const u8,
    key: crate::fz_value::ValueSlot,
) -> Option<crate::fz_value::ValueSlot> {
    let count = unsafe { crate::fz_value::map_count(p) };
    for i in 0..count {
        let (entry_key, entry_value) = unsafe { crate::fz_value::map_entry(p, i) };
        if map_key_cmp(entry_key, key).is_eq() {
            return Some(entry_value);
        }
    }
    None
}

fn map_value_keys_equal(a: crate::fz_value::ValueSlot, b: crate::fz_value::ValueSlot) -> bool {
    eq_value(a, b)
}

fn map_entry_by_matcher_value_key(
    p: *const u8,
    key: crate::fz_value::ValueSlot,
) -> Option<crate::fz_value::ValueSlot> {
    let count = unsafe { crate::fz_value::map_count(p) };
    for i in 0..count {
        let (entry_key, entry_value) = unsafe { crate::fz_value::map_entry(p, i) };
        if map_value_keys_equal(entry_key, key) {
            return Some(entry_value);
        }
    }
    None
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_begin() {
    current_process().map_builder = Some(Vec::new());
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_clone(base_bits: u64) {
    let mut entries = Vec::new();
    let p = current_heap_map_addr(base_bits).expect("fz_map_clone base not a heap map ptr");
    let count = unsafe { crate::fz_value::map_count(p) };
    for i in 0..count {
        let (k, v) = unsafe { crate::fz_value::map_entry(p, i) };
        entries.push((k, v));
    }
    current_process().map_builder = Some(entries);
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_push_typed(key_value: u64, key_kind: u8, val_value: u64, val_kind: u8) {
    let key = value_slot_from_parts(key_value, key_kind);
    let val = value_slot_from_parts(val_value, val_kind);
    current_process()
        .map_builder
        .as_mut()
        .expect("fz_map_push_typed without begin/clone")
        .push((key, val));
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_finalize() -> u64 {
    let raw = current_process()
        .map_builder
        .take()
        .expect("fz_map_finalize without begin");
    // Last write wins on duplicate keys: walk in order, dedupe-overwriting.
    let mut by_key = Vec::with_capacity(raw.len());
    for (k, v) in raw {
        if let Some(slot) = by_key
            .iter_mut()
            .find(|(ek, _)| map_key_cmp(*ek, k).is_eq())
        {
            slot.1 = v;
        } else {
            by_key.push((k, v));
        }
    }
    by_key.sort_by(|a, b| map_key_cmp(a.0, b.0));
    current_process().heap.alloc_map_slots(&by_key)
}

fn fz_map_get_value_typed(
    map_bits: u64,
    key_value: u64,
    key_kind: u8,
) -> Option<crate::fz_value::ValueSlot> {
    let key = value_slot_from_parts(key_value, key_kind);
    fz_map_get_value_by_key(map_bits, key)
}

fn fz_map_get_value_by_key(
    map_bits: u64,
    key: crate::fz_value::ValueSlot,
) -> Option<crate::fz_value::ValueSlot> {
    if let Some(p) = current_heap_resource_addr(map_bits) {
        let _ = key;
        let rs = unsafe { crate::resource::ResourceStub::from_raw(p) };
        return Some(rs.payload_value());
    }
    let Some(p) = current_heap_map_addr(map_bits) else {
        panic!("fz_map_get on non-ptr");
    };
    map_entry_by_value_key(p, key)
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_get_ref(map_ref_word: u64, key_ref_word: u64) -> u64 {
    let map = tagged_ref_from_word(map_ref_word, "fz_map_get_ref map");
    let key = tagged_ref_from_word(key_ref_word, "fz_map_get_ref key");
    current_process()
        .heap
        .read_map_value_ref(map, key)
        .expect("fz_map_get_ref")
        .unwrap_or_else(TaggedValueRef::null)
        .raw_word()
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_get_f64_typed(map_bits: u64, key_value: u64, key_kind: u8) -> f64 {
    use crate::fz_value::ValueKind;
    let Some(value) = fz_map_get_value_typed(map_bits, key_value, key_kind) else {
        panic!("fz_map_get_f64_typed: missing key");
    };
    match value.kind {
        ValueKind::FLOAT => f64::from_bits(value.raw),
        ValueKind::INT => value.raw as i64 as f64,
        _ => panic!("fz_map_get_f64_typed: value is not Float"),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_is_map(bits: u64) -> u8 {
    current_heap_map_addr(bits).is_some() as u8
}

// ===== Alloc cluster (fz-ul4.23.4.7) =====

#[unsafe(no_mangle)]
pub extern "C" fn fz_alloc_list_cons_typed(head_value: u64, head_kind: u8, tail_bits: u64) -> u64 {
    let head = value_slot_from_parts(head_value, head_kind);
    let p = current_process().heap.alloc(16);
    unsafe {
        std::ptr::write(
            p as *mut crate::fz_value::ListCons,
            crate::fz_value::ListCons::from_value_head(head, tail_bits),
        );
    }
    crate::fz_value::tagged_list_bits(p)
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_alloc_list_cell_uninit() -> u64 {
    // Codegen-only escape hatch: the emitted CLIF must store head and link
    // before any later call can observe the process heap.
    current_process().heap.alloc(16) as u64
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_list_is_cons(bits: u64) -> u8 {
    current_heap_list_addr(bits).is_some() as u8
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_list_head_ref(list_ref_word: u64) -> u64 {
    let list = tagged_ref_from_word(list_ref_word, "fz_list_head_ref");
    current_process()
        .heap
        .read_list_head_ref(list)
        .expect("fz_list_head_ref")
        .raw_word()
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_list_tail(bits: u64) -> u64 {
    let p = current_heap_list_addr(bits)
        .unwrap_or_else(|| panic!("fz_list_tail on empty/null/non-heap list {bits:#x}"));
    unsafe { (*(p as *const crate::fz_value::ListCons)).tail_bits() }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_list_tail_ref(list_ref_word: u64) -> u64 {
    let list = tagged_ref_from_word(list_ref_word, "fz_list_tail_ref");
    current_process()
        .heap
        .read_list_tail_ref(list)
        .expect("fz_list_tail_ref")
        .raw_word()
}

/// Allocate a heap-typed Struct. `schema_id` must already be registered in
/// the current Process's heap SchemaRegistry (shared with CompiledModule).
/// Returns a TAG_STRUCT-tagged heap pointer. Caller is
/// responsible for writing field values into payload slots after allocation.
#[unsafe(no_mangle)]
pub extern "C" fn fz_alloc_struct(schema_id: u32) -> u64 {
    let p = current_process().heap.alloc_struct(schema_id);
    crate::fz_value::tagged_struct_bits(p)
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_struct_get_field_ref(struct_ref_word: u64, field_offset: u32) -> u64 {
    let value = tagged_ref_from_word(struct_ref_word, "fz_struct_get_field_ref");
    current_process()
        .heap
        .read_struct_field_ref(value, field_offset)
        .expect("fz_struct_get_field_ref")
        .raw_word()
}

/// Allocate a frame for fn `fn_id`, looking up its size in the current
/// Process's frame_sizes table populated at make_process() time.
#[unsafe(no_mangle)]
pub extern "C" fn fz_alloc_frame_dyn(fn_id: u32) -> *mut u8 {
    let size = *current_process()
        .frame_sizes
        .get(fn_id as usize)
        .unwrap_or_else(|| panic!("frame_sizes has no entry for fn_id {}", fn_id));
    fz_alloc_frame(fn_id, size)
}

/// Public wrapper around the internal frame allocator. Used by the
/// Runtime in src/runtime.rs to spawn a task's entry frame and by
/// ir_codegen for the synchronous run path.
pub fn fz_alloc_frame_for_test(schema_id: u32, total_size: u32) -> *mut u8 {
    fz_alloc_frame(schema_id, total_size)
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
pub extern "C" fn fz_alloc_frame(schema_id: u32, total_size: u32) -> *mut u8 {
    FRAME_ALLOC_COUNT.with(|c| c.set(c.get() + 1));
    use std::alloc::{Layout, alloc_zeroed};
    // Round size up to a multiple of 16 to keep allocator happy and ensure
    // the resulting block aligns whatever follows.
    let rounded = ((total_size as usize) + 15) & !15;
    let layout = Layout::from_size_align(rounded, 16).expect("bad frame layout");
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

/// # Safety
///
/// `frame` must point to a live frame allocation whose schema contains
/// `field_offset` as an ValueSlot field.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_frame_store_value(
    frame: *mut u8,
    field_offset: u32,
    raw: u64,
    kind: u8,
) {
    let schema_id = unsafe { std::ptr::read(frame.add(8) as *const u32) };
    let schemas = current_process().heap.schemas.borrow();
    let kind_offset = schemas.get(schema_id).value_field_kind_offset(field_offset);
    unsafe {
        std::ptr::write(frame.add(16 + field_offset as usize) as *mut u64, raw);
        std::ptr::write(frame.add(kind_offset as usize), kind);
    }
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
pub extern "C" fn fz_value_eq_typed(a_raw: u64, a_kind: u8, b_raw: u64, b_kind: u8) -> u64 {
    let a = crate::fz_value::ValueSlot::decode_parts(a_raw, a_kind).expect("eq lhs kind");
    let b = crate::fz_value::ValueSlot::decode_parts(b_raw, b_kind).expect("eq rhs kind");
    u64::from(eq_value(a, b))
}

fn eq_value(a: crate::fz_value::ValueSlot, b: crate::fz_value::ValueSlot) -> bool {
    use crate::fz_value::ValueKind;
    if matches!(a.kind(), ValueKind::BITSTRING | ValueKind::PROCBIN)
        && matches!(b.kind(), ValueKind::BITSTRING | ValueKind::PROCBIN)
    {
        let ap = a.tagged_heap_bits().expect("bitstring lhs heap bits") as *mut u8;
        let bp = b.tagged_heap_bits().expect("bitstring rhs heap bits") as *mut u8;
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
                eq_list(a.raw() as *mut u8, b.raw() as *mut u8)
            }
        }
        ValueKind::MAP => eq_map(a.raw() as *mut u8, b.raw() as *mut u8),
        ValueKind::STRUCT => {
            let a_schema = unsafe { crate::fz_value::struct_schema_id(a.raw() as *const u8) };
            let b_schema = unsafe { crate::fz_value::struct_schema_id(b.raw() as *const u8) };
            eq_struct(a.raw() as *mut u8, b.raw() as *mut u8, a_schema, b_schema)
        }
        ValueKind::BITSTRING | ValueKind::PROCBIN => unreachable!("handled before kind check"),
        _ => false,
    }
}

fn eq_list(ap: *mut u8, bp: *mut u8) -> bool {
    use crate::fz_value::ListCons;
    // Walk both chains in lockstep. NIL terminates both at the same step.
    let mut a = ap as *const u8;
    let mut b = bp as *const u8;
    loop {
        let ac = unsafe { &*(a as *const ListCons) };
        let bc = unsafe { &*(b as *const ListCons) };
        if ac.head_kind() != bc.head_kind() {
            return false;
        }
        if !eq_value(ac.head_value(), bc.head_value()) {
            return false;
        }
        // Decide each tail: NIL => done; Ptr to List => recurse; else mismatch.
        let at = ac.tail_bits();
        let bt = bc.tail_bits();
        if at == bt {
            return true; // both NIL (same scalar bits) — common terminator
        }
        // If either tail is non-list, the chains diverge.
        let anp = crate::fz_value::list_addr_from_tagged(at);
        let bnp = crate::fz_value::list_addr_from_tagged(bt);
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

fn eq_struct(ap: *mut u8, bp: *mut u8, a_schema: u32, b_schema: u32) -> bool {
    if a_schema != b_schema {
        return false;
    }
    let reg = current_process().heap.schemas_registry();
    let registry = reg.borrow();
    let schema = registry.get(a_schema);
    for field in &schema.fields {
        match field.kind {
            crate::heap::FieldKind::ValueSlot => {
                let av = current_process().heap.read_field_slot(ap, field.offset);
                let bv = current_process().heap.read_field_slot(bp, field.offset);
                if !eq_value(av, bv) {
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
    let a_bits = unsafe { crate::procbin::bitstring_bit_len(ap) };
    let b_bits = unsafe { crate::procbin::bitstring_bit_len(bp) };
    if a_bits != b_bits {
        return false;
    }
    let bit_len = a_bits as usize;
    let full_bytes = bit_len / 8;
    let trailing = bit_len % 8;
    let a_pay = unsafe { crate::procbin::bitstring_byte_ptr(ap) };
    let b_pay = unsafe { crate::procbin::bitstring_byte_ptr(bp) };
    for i in 0..full_bytes {
        if unsafe { *a_pay.add(i) != *b_pay.add(i) } {
            return false;
        }
    }
    if trailing > 0 {
        let mask: u8 = 0xFFu8 << (8 - trailing);
        let a_last = unsafe { *a_pay.add(full_bytes) } & mask;
        let b_last = unsafe { *b_pay.add(full_bytes) } & mask;
        if a_last != b_last {
            return false;
        }
    }
    true
}

fn eq_map(ap: *mut u8, bp: *mut u8) -> bool {
    let a_count = unsafe { crate::fz_value::map_count(ap as *const u8) };
    let b_count = unsafe { crate::fz_value::map_count(bp as *const u8) };
    if a_count != b_count {
        return false;
    }
    // Both maps store entries in canonical sort order (.11.13), so a
    // pairwise walk suffices — same key-position implies same key.
    for i in 0..a_count {
        let (ak, av) = unsafe { crate::fz_value::map_entry(ap as *const u8, i) };
        let (bk, bv) = unsafe { crate::fz_value::map_entry(bp as *const u8, i) };
        if ak.kind != bk.kind || av.kind != bv.kind {
            return false;
        }
        if !eq_value(ak, bk) {
            return false;
        }
        if !eq_value(av, bv) {
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
    let p = match bitstring_like_ptr(bs_bits) {
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
pub extern "C" fn fz_matcher_map_get_ref(map_ref_word: u64, key_ref_word: u64) -> u64 {
    let map = tagged_ref_from_word(map_ref_word, "fz_matcher_map_get_ref map");
    let key = tagged_ref_from_word(key_ref_word, "fz_matcher_map_get_ref key");
    current_process()
        .heap
        .read_map_value_ref(map, key)
        .expect("fz_matcher_map_get_ref")
        .unwrap_or_else(TaggedValueRef::null)
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
/// initialized bytes. `val_bits` is treated as an opaque ValueSlot.
#[unsafe(no_mangle)]
pub extern "C" fn fz_matcher_eq_bytes(val_bits: u64, bytes_ptr: u64, byte_len: u64) -> u32 {
    let Some(p) = bitstring_like_ptr(val_bits) else {
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
/// a runtime tag. The typer must have already certified that `b`
/// names a bitstring (typically a fresh `ConstBitstring` or the
/// output of `fz_bitstring_valid_utf8` after a positive check).
/// Returned bits are the input bits.
///
/// Exists as a named seam so the typer can attach the `utf8` brand to
/// the value's Descr at this call site (the type rule for the L3
/// desugaring pass references this extern by name).
#[unsafe(no_mangle)]
pub extern "C" fn fz_brand_bitstring_as_utf8(b: u64) -> u64 {
    b
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::heap::SchemaRegistry;
    use crate::procbin::{bitstring_bit_len, bitstring_byte_ptr};
    use crate::process::{CURRENT_PROCESS, Process};
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

    /// fz-axu.14 (R1) — valid UTF-8 byte-aligned bitstring → 1.
    #[test]
    fn fz_bitstring_valid_utf8_accepts_byte_aligned_utf8() {
        with_process(|| {
            let bytes = "héllo".as_bytes();
            let bits = fz_alloc_bitstring_const(
                bytes.as_ptr() as u64,
                bytes.len() as u64,
                (bytes.len() * 8) as u64,
            );
            assert_eq!(fz_bitstring_valid_utf8(bits), 1);
        });
    }

    /// Invalid byte sequence → 0.
    #[test]
    fn fz_bitstring_valid_utf8_rejects_bad_bytes() {
        with_process(|| {
            let bytes = [0xffu8, 0xffu8];
            let bits = fz_alloc_bitstring_const(bytes.as_ptr() as u64, 2, 16);
            assert_eq!(fz_bitstring_valid_utf8(bits), 0);
        });
    }

    /// Non-byte-aligned bitstring → 0 even if the byte payload would
    /// be valid UTF-8 — UTF-8 is byte-oriented.
    #[test]
    fn fz_bitstring_valid_utf8_rejects_non_byte_aligned() {
        with_process(|| {
            let bytes = [b'h'];
            let bits = fz_alloc_bitstring_const(bytes.as_ptr() as u64, 1, 7);
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

    /// fz-cty.8 — small (<= threshold) payload allocates inline Bitstring.
    #[test]
    fn alloc_bitstring_const_small_payload_is_inline() {
        with_process(|| {
            let bytes: [u8; 3] = [0xaa, 0xbb, 0xcc];
            let bits = fz_alloc_bitstring_const(bytes.as_ptr() as u64, 3, 24);
            assert!(crate::fz_value::bitstring_addr_from_tagged(bits).is_some());
            unsafe {
                assert_eq!(
                    bits & crate::fz_value::TAG_MASK,
                    crate::fz_value::TAG_BITSTRING,
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
            let bits = fz_alloc_procbin_from_static(sb_ptr as u64);
            assert!(crate::fz_value::procbin_addr_from_tagged(bits).is_some());
            unsafe {
                assert_eq!(
                    bits & crate::fz_value::TAG_MASK,
                    crate::fz_value::TAG_PROCBIN
                );
                assert_eq!(crate::fz_value::object_size(bits), 16);
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
            let bits =
                fz_alloc_bitstring_const(payload.as_ptr() as u64, payload.len() as u64, 70 * 8);
            assert!(crate::fz_value::procbin_addr_from_tagged(bits).is_some());
            unsafe {
                assert_eq!(
                    bits & crate::fz_value::TAG_MASK,
                    crate::fz_value::TAG_PROCBIN
                );
                assert_eq!(crate::fz_value::object_size(bits), 16);
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
