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
//!   .10 vec     (fz_vec_*)
//!   .11 closure (fz_closure_*, fz_tail_closure)
//!   .12 concurrency (fz_spawn, fz_self, fz_send, fz_receive_attempt)
//!   .13 halt/print (fz_halt, fz_print_value)
//!
//! All fns here have unstable `extern "C"` ABI — they're called by
//! Cranelift-emitted code via the symbol-binding list in
//! `ir_codegen::compile`. Do not reorder args or change return types
//! without updating the matching `declare_function` signatures.

use crate::process::current_process;

// ===== Halt + print cluster (fz-ul4.23.4.13) =====

#[unsafe(no_mangle)]
pub extern "C" fn fz_print_value(fz_bits: u64) {
    let s = crate::fz_value::debug::render(fz_bits);
    // Always write to stdout so user-facing `fz run` / piped programs
    // see output. Also capture into TEST_CAPTURE so unit tests that
    // assert on print output keep working (cargo's stdout capture
    // means the println below is invisible during `cargo test`).
    println!("{}", s);
    TEST_CAPTURE.with(|c| c.borrow_mut().push(s));
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

/// Halt: receives an FzValue from the JIT, unboxes per-tag into a
/// debug-friendly i64 stored on the current Process's halt_value. Halt is a
/// debugging seam; this preserves byte-for-byte halt values for existing
/// scalar tests while not constraining heap-typed semantics later.
///
/// The second arg is the per-fn ABI's `ctx: *mut u8` (= *mut Process). For
/// the migration we ignore it in favor of current_process() — they point at
/// the same Process, but using current_process() keeps the access pattern
/// uniform with every other fz_* fn.
/// fz-cps.1.2 — `fz_halt` variant that doesn't take a host_ctx parameter.
/// Cont fns per docs/cps-in-clif.md §2.1 have sig `(result, self) tail`
/// with no host_ctx, so when their IR contains `Term::Halt(v)` they
/// invoke this version which pulls the current process from TLS.
///
/// Currently a one-liner wrapper around `fz_halt`; once the trampoline
/// goes away and uniform fns get rewritten, `fz_halt` itself may
/// migrate to this signature.
#[unsafe(no_mangle)]
pub extern "C" fn fz_halt_implicit(fz_bits: u64) {
    fz_halt(std::ptr::null_mut(), fz_bits);
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
pub extern "C" fn fz_halt(_ctx: *mut u8, fz_bits: u64) {
    use crate::fz_value::{FzValue, HeapKind, Tag};
    let v = FzValue(fz_bits);
    let i: i64 = match v.tag() {
        Tag::Int => v.unbox_int().unwrap(),
        // fz-yan.1 — nil/true/false are atoms with reserved IDs
        // (0/1/2), so they flow through this arm uniformly. Pre-yan
        // the Tag::Special branch returned true→1, false→0, nil→0;
        // post-yan they return their atom IDs (true→1 unchanged,
        // false→2 changed, nil→0 unchanged). Tests that asserted on
        // false's halt value need to assert 2 instead of 0.
        Tag::Atom => v.unbox_atom().unwrap() as i64,
        Tag::Ptr => {
            let p = v.unbox_ptr().unwrap();
            // Null Ptr-tagged value (e.g. 0): nothing to read, return raw bits.
            if p.is_null() {
                fz_bits as i64
            } else {
                let kind = unsafe { (*p).kind };
                // For boxed floats, halt returns the f64 bits so tests can
                // round-trip via f64::from_bits. Other heap kinds: raw bits.
                match HeapKind::from_u16(kind) {
                    Some(HeapKind::Float) => crate::heap::Heap::read_float(p).to_bits() as i64,
                    _ => fz_bits as i64,
                }
            }
        }
        Tag::Reserved => fz_bits as i64,
    };
    current_process().halt_value = i;
}

// ===== Concurrency cluster (fz-ul4.23.4.12) =====

/// fz-ul4.19.2: scheduler-bound builtins.
///
/// Both consume a Runtime installed in TLS by Runtime::run_until_idle.
/// Calling either outside the scheduler path panics with a clear message.
///
/// fz_spawn(closure_bits) -> pid_bits. fz-ul4.29.5 lift: dispatches the
/// closure (with any number of captures) to the scheduler hook. The hook
/// deep-copies the closure into the new task's heap, materializes the
/// initial frame via the closure's stub_fp, and enqueues. Returns the
/// new pid as a boxed FzValue Int.
#[unsafe(no_mangle)]
pub extern "C" fn fz_spawn(closure_bits: u64) -> u64 {
    use crate::fz_value::FzValue;
    let _cp = FzValue(closure_bits)
        .unbox_ptr()
        .expect("spawn: closure not a heap ptr");
    let pid = crate::scheduler_hooks::dispatch_spawn(closure_bits);
    FzValue::from_int(pid as i64).0
}

/// fz-siu.12: fz_spawn_opt(closure_bits, min_heap_size_bits) -> pid_bits.
/// Like fz_spawn but accepts a min_heap_size hint as a tagged FzValue int
/// (bytes). v1: hint is accepted and ignored.
#[unsafe(no_mangle)]
pub extern "C" fn fz_spawn_opt(closure_bits: u64, min_heap_size_bits: u64) -> u64 {
    use crate::fz_value::FzValue;
    let _cp = FzValue(closure_bits)
        .unbox_ptr()
        .expect("spawn_opt: closure not a heap ptr");
    let min_heap_size = FzValue(min_heap_size_bits).unbox_int().unwrap_or(0) as u32;
    let pid = crate::scheduler_hooks::dispatch_spawn_opt(closure_bits, min_heap_size);
    FzValue::from_int(pid as i64).0
}

/// fz-swt.10 — `make_resource(payload, dtor)` runtime BIF, callable from
/// the JIT/AOT path. `payload` is the raw FzValue bits to hand back to the
/// user-supplied dtor; `dtor_closure_bits` is the closure value produced
/// by the `&name/arity` form. Returns the FzValue bits of the resource
/// handle (a `HeapKind::Resource` stub on the current process heap).
///
/// Dtor resolution requires walking the closure body's IR to find the
/// underlying `Prim::Extern`, so we delegate to the binary-side hook
/// (the runtime crate has no IR Module). The same hook is installed for
/// both interp and JIT/AOT execution — the symbol path is therefore
/// uniform across all three legs (see fz-swt.10's `MakeResourceHook`).
#[unsafe(no_mangle)]
pub extern "C" fn fz_make_resource(payload: u64, dtor_closure_bits: u64) -> u64 {
    crate::scheduler_hooks::dispatch_make_resource(payload, dtor_closure_bits)
}

/// fz_self() -> pid_bits. Returns the currently-running task's pid as a
/// boxed FzValue Int.
#[unsafe(no_mangle)]
pub extern "C" fn fz_self() -> u64 {
    use crate::fz_value::FzValue;
    FzValue::from_int(current_process().pid as i64).0
}

/// fz-ht5 — process-global monotonic counter feeding `fz_make_ref`.
/// Starts at 1 so 0 can remain a "no ref" sentinel if a future ticket
/// needs one. AtomicU64 + Relaxed is sufficient under single-worker
/// today and remains correct under future multi-worker.
static FZ_NEXT_REF: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

/// fz_make_ref() -> ref_bits. Mints a fresh opaque ref by atomically
/// incrementing the process-global counter and tagging the result as a
/// boxed FzValue Int. The 61-bit Int range (FzValue::INT_MAX ≈ 1.15e18)
/// is the practical capacity; debug builds assert before tagging.
#[unsafe(no_mangle)]
pub extern "C" fn fz_make_ref() -> u64 {
    use crate::fz_value::FzValue;
    let id = FZ_NEXT_REF.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    debug_assert!(
        id <= FzValue::INT_MAX as u64,
        "fz_make_ref: exhausted 61-bit ref space"
    );
    FzValue::from_int(id as i64).0
}

/// fz_send(receiver_pid_bits, msg_bits) -> msg_bits.
///
/// Deep-copies msg into the receiver's heap, enqueues into receiver's
/// mailbox, transitions receiver from Blocked to Ready (and re-enqueues)
/// if it was waiting.
///
/// v1 limitations:
/// - Receiver must be a task currently in the Runtime's task registry
///   (panics otherwise).
/// - deep_copy_value supports List, Struct (tuple/closure/map structurally
///   covered), Bitstring, and scalars. Other HeapKinds panic with an
///   explicit message; follow-up tickets extend coverage.
#[unsafe(no_mangle)]
pub extern "C" fn fz_send(receiver_pid_bits: u64, msg_bits: u64) -> u64 {
    use crate::fz_value::FzValue;
    let receiver_pid = FzValue(receiver_pid_bits)
        .unbox_int()
        .expect("send: pid not Int") as u32;
    crate::scheduler_hooks::dispatch_send(receiver_pid, msg_bits);
    msg_bits
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
/// param (Tagged FzValue); `self` is the cont closure ptr itself.
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
        unsafe {
            let result_slot = cont_frame_ptr.add(24) as *mut u64;
            std::ptr::write(result_slot, msg.0);
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
    p.mid_flight_roots.as_mut_ptr() as *mut u64
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
/// Caller writes stub_fp at offset 16 and captures at offset 24+.
/// `halt_kind` (fz-ul4.27.22.6) is packed into the closure header's
/// `flags` so `fz_spawn_entry` and `fz_resume_park` can pick the matching
/// halt-cont singleton at task launch.
#[unsafe(no_mangle)]
pub extern "C" fn fz_alloc_closure(callee_fn_id: u32, captured_count: u32, halt_kind: u32) -> u64 {
    FRAME_ALLOC_COUNT.with(|c| c.set(c.get() + 1));
    let p = current_process().heap.alloc_closure(
        callee_fn_id,
        captured_count as usize,
        halt_kind as u16,
    );
    p as u64
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
    use crate::fz_value::{HeapHeader, HeapKind};
    let mut buf: Box<[u64; 3]> = Box::new([0u64; 3]);
    let base = buf.as_mut_ptr() as *mut u8;
    let header = HeapHeader {
        kind: HeapKind::Closure as u16,
        flags: 0,
        size_bytes: 24,
        schema_id: 0,
        _reserved: 0,
    };
    unsafe {
        std::ptr::write(base as *mut HeapHeader, header);
        std::ptr::write(base.add(16) as *mut u64, halt_cont_body_addr);
    }
    p.halt_cont_singletons[slot] = base;
    p.static_closure_bufs.push(buf);
    base as u64
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
    // HeapHeader. Linear in static_closures.len() — small (one entry
    // per zero-cap closure-target spec).
    for ptr in &p.static_closures {
        if ptr.is_null() {
            continue;
        }
        let header = unsafe { &*(*ptr as *const crate::fz_value::HeapHeader) };
        if header._reserved == cl_sid {
            return *ptr as u64;
        }
    }
    panic!(
        "fz_get_static_closure: no singleton for cl_sid/fn_id {} ({} entries)",
        cl_sid,
        p.static_closures.len()
    );
}

// ===== Vec cluster (fz-ul4.23.4.10) =====
//
// Vecs are heap objects with raw element-payload (no FzValues inside).
// Construction stages elements in TLS via begin(kind) -> push(v) ×n ->
// finalize(); per-kind decoding happens at push (for U8/Bit) or finalize
// (Bit packs at the end). VecF64 is gated behind .11.20/.11.23.

#[derive(Debug)]
pub enum VecBuild {
    I64(Vec<i64>),
    U8(Vec<u8>),
    Bit(Vec<bool>),
}

/// kind tag matches `HeapKind as u16`: VecI64=3, VecU8=5, VecBit=6.
#[unsafe(no_mangle)]
pub extern "C" fn fz_vec_begin(kind_tag: u32) {
    use crate::fz_value::HeapKind;
    let b = match HeapKind::from_u16(kind_tag as u16) {
        Some(HeapKind::VecI64) => VecBuild::I64(Vec::new()),
        Some(HeapKind::VecU8) => VecBuild::U8(Vec::new()),
        Some(HeapKind::VecBit) => VecBuild::Bit(Vec::new()),
        Some(HeapKind::VecF64) => panic!("VecF64 deferred to fz-ul4.11.23"),
        _ => panic!("fz_vec_begin: invalid kind tag {}", kind_tag),
    };
    current_process().vec_builder = Some(b);
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_vec_push(value_bits: u64) {
    use crate::fz_value::FzValue;
    let n = FzValue(value_bits)
        .unbox_int()
        .expect("fz_vec_push: vec element not Int");
    match current_process()
        .vec_builder
        .as_mut()
        .expect("fz_vec_push without begin")
    {
        VecBuild::I64(v) => v.push(n),
        VecBuild::U8(v) => v.push(n as u8),
        VecBuild::Bit(v) => v.push(n != 0),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_vec_finalize() -> u64 {
    let b = current_process()
        .vec_builder
        .take()
        .expect("fz_vec_finalize without begin");
    let heap = &mut current_process().heap;
    let p = match b {
        VecBuild::I64(v) => heap.alloc_vec_i64(&v),
        VecBuild::U8(v) => heap.alloc_vec_u8(&v),
        VecBuild::Bit(v) => heap.alloc_vec_bit(&v),
    };
    p as u64
}

/// vec_get(vec, index) -> element as FzValue Int (for I64/U8/Bit).
/// Out-of-bounds returns FzValue::NIL (mirrors Map's missing-key behavior).
#[unsafe(no_mangle)]
pub extern "C" fn fz_vec_get(vec_bits: u64, index_bits: u64) -> u64 {
    use crate::fz_value::{FzValue, HeapKind};
    let p = FzValue(vec_bits)
        .unbox_ptr()
        .expect("fz_vec_get: vec not a heap ptr");
    let header = unsafe { &*p };
    let i = FzValue(index_bits)
        .unbox_int()
        .expect("fz_vec_get: index not Int") as usize;
    let len = crate::heap::Heap::vec_len(p) as usize;
    if i >= len {
        return FzValue::NIL.0;
    }
    let payload = unsafe { (p as *const u8).add(24) };
    let n: i64 = match HeapKind::from_u16(header.kind) {
        Some(HeapKind::VecI64) => unsafe { std::ptr::read((payload as *const i64).add(i)) },
        Some(HeapKind::VecU8) => unsafe { *payload.add(i) as i64 },
        Some(HeapKind::VecBit) => {
            let byte_idx = i / 8;
            let bit_idx = 7 - (i % 8);
            let byte = unsafe { *payload.add(byte_idx) };
            ((byte >> bit_idx) & 1) as i64
        }
        Some(HeapKind::VecF64) => panic!("VecF64 deferred to fz-ul4.11.23"),
        _ => panic!("fz_vec_get on non-vec heap kind"),
    };
    FzValue::from_int(n).0
}

// ===== Bitstring cluster (fz-ul4.23.4.9) =====

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
pub extern "C" fn fz_bs_write_field(
    value_bits: u64,
    ty_tag: u32,
    size_present: u32,
    size_value: u32,
    unit: u32,
    endian_tag: u32,
    signed: u32,
) {
    use crate::bitstr::BitType;
    use crate::fz_value::{FzValue, Tag};
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
                let n = FzValue(value_bits)
                    .unbox_int()
                    .expect("integer bit field expects boxed int");
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
                let v = FzValue(value_bits);
                let p = match v.tag() {
                    Tag::Ptr => v.unbox_ptr().expect("binary field: bad ptr"),
                    _ => panic!("binary/bits bit field expects heap bitstring"),
                };
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
                let cp = FzValue(value_bits)
                    .unbox_int()
                    .expect("utf field expects integer codepoint") as u32;
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
                // Decode the FzValue: Int unboxes to i64 then casts to f64;
                // boxed Float reads payload directly. Then bit-cast and write.
                let f = fz_to_f64(value_bits);
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
    p as u64
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
    p as u64
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
    pb.as_raw() as u64
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
pub extern "C" fn fz_bs_reader_init(bs_bits: u64) -> u64 {
    use crate::fz_value::{FzValue, Tag};
    let v = FzValue(bs_bits);
    let p = match v.tag() {
        Tag::Ptr => v.unbox_ptr().expect("reader_init: bad ptr"),
        _ => panic!("reader_init expects heap value"),
    };
    if !unsafe { crate::procbin::is_bitstring_like(p) } {
        panic!("reader_init source is not a Bitstring");
    }
    let bit_len = unsafe { crate::procbin::bitstring_bit_len(p) } as i64;
    let arity3 = current_process()
        .bs_tuple_arity3_schema
        .expect("bs_tuple_arity3_schema not set");
    let tuple_p = current_process().heap.alloc_struct(arity3);
    unsafe {
        let base = (tuple_p as *mut u8).add(16);
        // [bs_ptr, bit_len_boxed, 0_boxed]
        std::ptr::write(base as *mut u64, bs_bits);
        std::ptr::write(base.add(8) as *mut u64, ((bit_len as u64) << 3) | 0b001);
        std::ptr::write(base.add(16) as *mut u64, ((0i64 as u64) << 3) | 0b001);
    }
    tuple_p as u64
}

#[allow(clippy::too_many_arguments)]
#[unsafe(no_mangle)]
pub extern "C" fn fz_bs_read_field(
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
    use crate::fz_value::FzValue;
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
    let v = FzValue(reader_bits);
    let rp = v.unbox_ptr().expect("read_field: reader is not a ptr");
    let bs_bits = unsafe { std::ptr::read((rp as *const u8).add(16) as *const u64) };
    let bit_len = (FzValue(unsafe { std::ptr::read((rp as *const u8).add(24) as *const u64) }))
        .unbox_int()
        .unwrap() as usize;
    let pos = (FzValue(unsafe { std::ptr::read((rp as *const u8).add(32) as *const u64) }))
        .unbox_int()
        .unwrap() as usize;

    // Bytes pointer from bs.
    let bs_v = FzValue(bs_bits);
    let bsp = bs_v.unbox_ptr().expect("read_field: reader bs not a ptr");
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
        unsafe {
            let base = (p as *mut u8).add(16);
            std::ptr::write(base as *mut u64, FzValue::FALSE.0);
        }
        p as u64
    };

    let mut r = crate::bitstr::BitReader {
        bytes,
        bit_len,
        pos,
    };

    let (extracted_bits, consumed) = match ty {
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
            (FzValue::from_int(n).0, total as usize)
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
            let new_bs_bits = new_bs as u64;
            (new_bs_bits, needed_bits)
        }
        BitType::Float => {
            let total = size.unwrap_or(64) * unit;
            if total != 32 && total != 64 {
                return fail();
            }
            let raw = match r.read_bits(total as usize) {
                Some(v) => v,
                None => return fail(),
            };
            let raw = apply_endian_for_read(raw, total, endian);
            let f = if total == 32 {
                f32::from_bits(raw as u32) as f64
            } else {
                f64::from_bits(raw)
            };
            let p = current_process().heap.alloc_float(f);
            (p as u64, total as usize)
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
    unsafe {
        let base = (new_reader_p as *mut u8).add(16);
        std::ptr::write(base as *mut u64, bs_bits);
        std::ptr::write(base.add(8) as *mut u64, ((bit_len as u64) << 3) | 0b001);
        std::ptr::write(base.add(16) as *mut u64, ((new_pos as u64) << 3) | 0b001);
    }

    // Allocate result tuple [true, extracted, new_reader].
    let result_p = current_process().heap.alloc_struct(arity3);
    unsafe {
        let base = (result_p as *mut u8).add(16);
        std::ptr::write(base as *mut u64, FzValue::TRUE.0);
        std::ptr::write(base.add(8) as *mut u64, extracted_bits);
        std::ptr::write(base.add(16) as *mut u64, new_reader_p as u64);
    }
    result_p as u64
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

fn fz_key_category(bits: u64) -> u8 {
    match bits & 0b111 {
        0b001 => 0,
        0b010 => 1,
        0b011 => 2,
        0b000 => 3,
        _ => 4,
    }
}

fn fz_key_cmp(a: u64, b: u64) -> std::cmp::Ordering {
    let ca = fz_key_category(a);
    let cb = fz_key_category(b);
    ca.cmp(&cb).then_with(|| {
        if ca == 0 {
            ((a as i64) >> 3).cmp(&((b as i64) >> 3))
        } else {
            a.cmp(&b)
        }
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_begin() {
    current_process().map_builder = Some(Vec::new());
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_clone(base_bits: u64) {
    use crate::fz_value::{FzValue, HeapKind};
    let mut entries: Vec<(u64, u64)> = Vec::new();
    let p = FzValue(base_bits)
        .unbox_ptr()
        .expect("fz_map_clone base not a heap ptr");
    let header = unsafe { &*p };
    if HeapKind::from_u16(header.kind) != Some(HeapKind::Map) {
        panic!("fz_map_clone base is not a Map");
    }
    let count = unsafe { std::ptr::read((p as *const u8).add(16) as *const u64) as usize };
    let mut cursor = unsafe { (p as *const u8).add(24) as *const u64 };
    for _ in 0..count {
        let k = unsafe { std::ptr::read(cursor) };
        let v = unsafe { std::ptr::read(cursor.add(1)) };
        cursor = unsafe { cursor.add(2) };
        entries.push((k, v));
    }
    current_process().map_builder = Some(entries);
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_push(key_bits: u64, val_bits: u64) {
    current_process()
        .map_builder
        .as_mut()
        .expect("fz_map_push without begin/clone")
        .push((key_bits, val_bits));
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_finalize() -> u64 {
    use crate::fz_value::FzValue;
    let raw = current_process()
        .map_builder
        .take()
        .expect("fz_map_finalize without begin");
    // Last write wins on duplicate keys: walk in order, dedupe-overwriting.
    let mut by_key: Vec<(u64, u64)> = Vec::with_capacity(raw.len());
    for (k, v) in raw {
        if let Some(slot) = by_key.iter_mut().find(|(ek, _)| fz_key_cmp(*ek, k).is_eq()) {
            slot.1 = v;
        } else {
            by_key.push((k, v));
        }
    }
    by_key.sort_by(|a, b| fz_key_cmp(a.0, b.0));
    let entries: Vec<(FzValue, FzValue)> = by_key
        .into_iter()
        .map(|(k, v)| (FzValue(k), FzValue(v)))
        .collect();
    let p = current_process().heap.alloc_map(&entries);
    p as u64
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_map_get(map_bits: u64, key_bits: u64) -> u64 {
    use crate::fz_value::{FzValue, HeapKind};
    let p = FzValue(map_bits)
        .unbox_ptr()
        .expect("fz_map_get on non-ptr");
    let header = unsafe { &*p };
    // fz-swt.8 — `handle.value` on a resource handle. The typer accepts
    // `.value` on opaque-typed handles (gated by declaring-module
    // visibility); the lowering reuses `m.k` → `Prim::MapGet`. At
    // runtime, a resource stub answers `:value` with its payload —
    // no map dispatch.
    //
    // We don't peek at `key_bits` here: the typer has already rejected
    // any non-`:value` access on a resource (no `.foo` exists), so the
    // runtime can return the payload unconditionally for Resource
    // subjects. If a future feature wants to grow more resource
    // accessors, this is where the dispatch would split.
    if HeapKind::from_u16(header.kind) == Some(HeapKind::Resource) {
        let _ = key_bits;
        // The 32-byte stub stores the off-heap Resource pointer at
        // offset +16 (mirrors `ResourceStub::shared_raw`); the
        // `payload` field on the Resource itself sits at offset +16
        // of the off-heap struct (see `Resource` layout assertion).
        let shared = unsafe {
            std::ptr::read((p as *const u8).add(16) as *const *mut crate::resource::Resource)
        };
        return unsafe { (*shared).payload };
    }
    if HeapKind::from_u16(header.kind) != Some(HeapKind::Map) {
        panic!("fz_map_get on non-Map");
    }
    let count = unsafe { std::ptr::read((p as *const u8).add(16) as *const u64) as usize };
    let cursor = unsafe { (p as *const u8).add(24) as *const u64 };
    // v1: linear scan. Sorted layout exists primarily so equality and
    // rendering have a deterministic shape; binary search comes alongside
    // a HAMT migration for large maps (separate ticket).
    for i in 0..count {
        let k = unsafe { std::ptr::read(cursor.add(i * 2)) };
        if fz_key_cmp(k, key_bits).is_eq() {
            return unsafe { std::ptr::read(cursor.add(i * 2 + 1)) };
        }
    }
    FzValue::NIL.0
}

// ===== Alloc cluster (fz-ul4.23.4.7) =====

#[unsafe(no_mangle)]
pub extern "C" fn fz_alloc_list_cons(head_bits: u64, tail_bits: u64) -> u64 {
    use crate::fz_value::FzValue;
    let p = current_process()
        .heap
        .alloc_list_cons(FzValue(head_bits), FzValue(tail_bits));
    // Heap returns 16-byte-aligned pointers (low 4 bits zero), so the raw
    // pointer doubles as the FzValue ptr-tagged encoding (tag bits = 000).
    p as u64
}

/// Allocate a heap-typed Struct. `schema_id` must already be registered in
/// the current Process's heap SchemaRegistry (shared with CompiledModule).
/// Returns the FzValue ptr-bits (heap-aligned, so tag = 000). Caller is
/// responsible for writing field values into payload slots after allocation.
#[unsafe(no_mangle)]
pub extern "C" fn fz_alloc_struct(schema_id: u32) -> u64 {
    let p = current_process().heap.alloc_struct(schema_id);
    p as u64
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_alloc_float(bits: u64) -> u64 {
    let f = f64::from_bits(bits);
    let p = current_process().heap.alloc_float(f);
    p as u64
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
        let hp = p as *mut crate::fz_value::HeapHeader;
        (*hp) = crate::fz_value::HeapHeader {
            kind: 0, // Struct
            flags: 0,
            size_bytes: total_size,
            schema_id,
            _reserved: 0,
        };
    }
    p
}

// ===== Arith / cmp / eq cluster (fz-ul4.23.4.1) =====

/// Decode an FzValue (Int or boxed Float) into f64. Panics on other tags.
pub fn fz_to_f64(bits: u64) -> f64 {
    use crate::fz_value::{FzValue, HeapKind, Tag};
    let v = FzValue(bits);
    match v.tag() {
        Tag::Int => v.unbox_int().unwrap() as f64,
        Tag::Ptr => {
            let p = v.unbox_ptr().unwrap();
            let kind = unsafe { (*p).kind };
            match HeapKind::from_u16(kind) {
                Some(HeapKind::Float) => crate::heap::Heap::read_float(p),
                _ => panic!("arithmetic on non-numeric heap kind {}", kind),
            }
        }
        _ => panic!("arithmetic on non-numeric tag {:?}", v.tag()),
    }
}

pub fn box_float(f: f64) -> u64 {
    let p = current_process().heap.alloc_float(f);
    p as u64
}

/// Tag-promotion helper for the JIT's mixed-type arithmetic slow path.
/// fz-ul4.27.9: replaced the per-op fz_arith_* / fz_cmp_* helpers — JIT now
/// promotes both operands here, then emits native Cranelift fadd/fcmp/etc
/// inline and (for arith) boxes the result via fz_alloc_float.
#[unsafe(no_mangle)]
pub extern "C" fn fz_promote_f64(bits: u64) -> f64 {
    fz_to_f64(bits)
}

/// f64 remainder (fmod-style: truncated, sign of dividend). Cranelift has no
/// frem opcode, so the JIT's float-mod slow path calls out here.
#[unsafe(no_mangle)]
pub extern "C" fn fz_fmod(a: f64, b: f64) -> f64 {
    a % b
}

/// Convert a Rust bool into FzValue TRUE/FALSE bits. Used by the interpreter
/// for cmp results; the JIT emits the equivalent inline.
pub fn cmp_to_fz(b: bool) -> u64 {
    use crate::fz_value::FzValue;
    if b { FzValue::TRUE.0 } else { FzValue::FALSE.0 }
}

/// Structural Eq for two Tag::Ptr FzValues. Both args MUST be Tag::Ptr —
/// the JIT-side dispatch (`both_ptr` test) guarantees this, so the unwraps
/// are infallible. Returns FzValue TRUE/FALSE bits.
///
/// Recursion: List/Struct/Map fields are themselves FzValues that may be
/// scalars or other heap values, so the recursive call dispatches on the
/// child's tag. For scalar children we can short-circuit on raw bit
/// equality before calling back into this fn — `eq_fz` handles that.
#[unsafe(no_mangle)]
pub extern "C" fn fz_value_eq(a: u64, b: u64) -> u64 {
    cmp_to_fz(eq_fz(a, b))
}

/// Internal recursive equality for FzValues of any tag. Scalars short-
/// circuit on bit-eq; heap-typed pairs of the same kind recurse per kind.
fn eq_fz(a: u64, b: u64) -> bool {
    use crate::fz_value::{FzValue, HeapKind, Tag};
    if a == b {
        return true;
    } // covers all scalar same-tag cases + ptr-identity
    let av = FzValue(a);
    let bv = FzValue(b);
    if !matches!((av.tag(), bv.tag()), (Tag::Ptr, Tag::Ptr)) {
        // At least one side is a scalar with different bits -> inequal.
        return false;
    }
    let ap = av.unbox_ptr().unwrap();
    let bp = bv.unbox_ptr().unwrap();
    if ap.is_null() || bp.is_null() {
        return ap == bp;
    }
    let ah = unsafe { &*ap };
    let bh = unsafe { &*bp };
    // fz-cty.5: a Bitstring and a ProcBin with equal bytes + bit_len are
    // semantically equal — storage kind is an implementation detail.
    let a_bs_like = unsafe { crate::procbin::is_bitstring_like(ap) };
    let b_bs_like = unsafe { crate::procbin::is_bitstring_like(bp) };
    if a_bs_like && b_bs_like {
        return eq_bitstring(ap, bp);
    }
    if ah.kind != bh.kind {
        return false;
    }
    match HeapKind::from_u16(ah.kind) {
        Some(HeapKind::Float) => {
            crate::heap::Heap::read_float(ap) == crate::heap::Heap::read_float(bp)
        }
        Some(HeapKind::List) => eq_list(ap, bp),
        Some(HeapKind::Struct) => eq_struct(ap, bp, ah.schema_id, bh.schema_id),
        Some(HeapKind::Map) => eq_map(ap, bp),
        // Closures + Vecs: ticket scope is List/Struct/Bitstring/Map only.
        // Fall back to ptr-identity (already false here, since a != b).
        _ => false,
    }
}

fn eq_list(ap: *mut crate::fz_value::HeapHeader, bp: *mut crate::fz_value::HeapHeader) -> bool {
    use crate::fz_value::{HeapKind, ListCons};
    // Walk both chains in lockstep. NIL terminates both at the same step.
    let mut a = ap as *const u8;
    let mut b = bp as *const u8;
    loop {
        let ac = unsafe { &*(a as *const ListCons) };
        let bc = unsafe { &*(b as *const ListCons) };
        if !eq_fz(ac.head.0, bc.head.0) {
            return false;
        }
        // Decide each tail: NIL => done; Ptr to List => recurse; else mismatch.
        let at = ac.tail.0;
        let bt = bc.tail.0;
        if at == bt {
            return true; // both NIL (same scalar bits) — common terminator
        }
        // If either tail is non-list, the chains diverge.
        let av = crate::fz_value::FzValue(at);
        let bv = crate::fz_value::FzValue(bt);
        let (Some(anp), Some(bnp)) = (av.unbox_ptr(), bv.unbox_ptr()) else {
            return false;
        };
        let ak = unsafe { (*anp).kind };
        let bk = unsafe { (*bnp).kind };
        if HeapKind::from_u16(ak) != Some(HeapKind::List)
            || HeapKind::from_u16(bk) != Some(HeapKind::List)
        {
            return false;
        }
        a = anp as *const u8;
        b = bnp as *const u8;
    }
}

fn eq_struct(
    ap: *mut crate::fz_value::HeapHeader,
    bp: *mut crate::fz_value::HeapHeader,
    a_schema: u32,
    b_schema: u32,
) -> bool {
    if a_schema != b_schema {
        return false;
    }
    // Schema in current Process's heap registry tells us field count.
    let n_fields = {
        let reg = current_process().heap.schemas_registry();
        let registry = reg.borrow();
        registry.get(a_schema).fields.len()
    };
    for i in 0..n_fields {
        let off = (i * 8) as isize;
        let av = unsafe { std::ptr::read((ap as *const u8).offset(16 + off) as *const u64) };
        let bv = unsafe { std::ptr::read((bp as *const u8).offset(16 + off) as *const u64) };
        if !eq_fz(av, bv) {
            return false;
        }
    }
    true
}

fn eq_bitstring(
    ap: *mut crate::fz_value::HeapHeader,
    bp: *mut crate::fz_value::HeapHeader,
) -> bool {
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

fn eq_map(ap: *mut crate::fz_value::HeapHeader, bp: *mut crate::fz_value::HeapHeader) -> bool {
    let a_count = unsafe { std::ptr::read((ap as *const u8).add(16) as *const u64) } as usize;
    let b_count = unsafe { std::ptr::read((bp as *const u8).add(16) as *const u64) } as usize;
    if a_count != b_count {
        return false;
    }
    // Both maps store entries in canonical sort order (.11.13), so a
    // pairwise walk suffices — same key-position implies same key.
    let a_cur = unsafe { (ap as *const u8).add(24) as *const u64 };
    let b_cur = unsafe { (bp as *const u8).add(24) as *const u64 };
    for i in 0..a_count {
        let ak = unsafe { std::ptr::read(a_cur.add(i * 2)) };
        let bk = unsafe { std::ptr::read(b_cur.add(i * 2)) };
        if !eq_fz(ak, bk) {
            return false;
        }
        let av = unsafe { std::ptr::read(a_cur.add(i * 2 + 1)) };
        let bv = unsafe { std::ptr::read(b_cur.add(i * 2 + 1)) };
        if !eq_fz(av, bv) {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_value::HeapKind;
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

    /// fz-cty.8 — small (<= threshold) payload allocates inline Bitstring.
    #[test]
    fn alloc_bitstring_const_small_payload_is_inline() {
        with_process(|| {
            let bytes: [u8; 3] = [0xaa, 0xbb, 0xcc];
            let bits = fz_alloc_bitstring_const(bytes.as_ptr() as u64, 3, 24);
            let p = crate::fz_value::FzValue(bits).unbox_ptr().unwrap();
            unsafe {
                assert_eq!(
                    HeapKind::from_u16((*p).kind),
                    Some(HeapKind::Bitstring),
                    "small payload should pick the inline Bitstring kind"
                );
                assert_eq!(bitstring_bit_len(p), 24);
                let bp = bitstring_byte_ptr(p);
                assert_eq!(std::slice::from_raw_parts(bp, 3), &bytes);
            }
        });
    }

    /// fz-q8d.2 — `fz_alloc_procbin_from_static` retains the static
    /// SharedBin's anchor (climbing 1 → 2), allocates a ProcBin that
    /// owns the new edge, and returns it as a tagged FzValue ptr. When
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
            let p = crate::fz_value::FzValue(bits).unbox_ptr().unwrap();
            unsafe {
                assert_eq!(HeapKind::from_u16((*p).kind), Some(HeapKind::ProcBin));
                assert_eq!(bitstring_bit_len(p), 64);
                let bp = bitstring_byte_ptr(p);
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
            let p = crate::fz_value::FzValue(bits).unbox_ptr().unwrap();
            unsafe {
                assert_eq!(
                    HeapKind::from_u16((*p).kind),
                    Some(HeapKind::ProcBin),
                    "large payload should route through ProcBin / SharedBin"
                );
                assert_eq!(bitstring_bit_len(p), 70 * 8);
                let bp = bitstring_byte_ptr(p);
                assert_eq!(
                    std::slice::from_raw_parts(bp, payload.len()),
                    payload.as_slice()
                );
            }
        });
    }
}
