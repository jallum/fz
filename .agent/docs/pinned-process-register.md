# Pinned Process Register

Every running fz task is a `Process`. Code that runs under a task needs to name
"my process" to spend its reduction budget, allocate on its heap, and pass it to
runtime helpers. There is no ambient global for this. Instead each engine carries
the current `Process*` explicitly, and the two engines carry it differently:

- **Compiled code** keeps the `Process*` in a Cranelift **pinned register**, a
  general-purpose register that Cranelift removes from normal allocation so its
  value stays put for the whole function invocation.
- **The interpreter** holds the `Process*` in a per-instance field
  (`IrInterpRuntime::current_proc`, set per quantum, read via `cur_proc`).

Both replace what would otherwise be a thread-local "current process". Threading
the process explicitly — never through a process-wide global — is what lets two
schedulers (or two interpreters) be live at once on one worker thread without
clobbering each other.

This doc covers the compiled half: the register, the offset ABI codegen reads
through it, and the host wrappers that install it at the engine boundary.

## The register

`enable_pinned_reg` is set on the shared host-ISA builder (`host_isa_with` in
`src/ir_codegen/clif.rs`), which both engines use: the JIT builds it with
`is_pic = false`, AOT with `is_pic = true`. With the flag on, CLIF may use
`get_pinned_reg` / `set_pinned_reg`, and Cranelift drops the register from its
allocatable set. Which register it is, is architecture-selected by Cranelift, not
chosen here:

- x64: `r15`
- aarch64: `x21`

## Process ABI surface

Codegen depends on a small, explicit offset contract — never on the whole Rust
`Process` layout. `runtime/src/process_abi.rs` owns it:

```rust
pub const PROCESS_REDUCTIONS_REMAINING_OFFSET: i32 = offset_of!(Process, reductions_remaining) as i32;
pub const PROCESS_YIELD_REASONS_OFFSET: i32 = offset_of!(Process, yield_reasons) as i32;
```

`reductions_remaining` is an `i32` (the per-quantum budget); `yield_reasons` is a
`u8` of pending reason bits. Each offset has a test (`process_abi_test.rs`)
asserting the constant equals the field's real byte offset (`field_addr -
base_addr`) in a live `Process`. Only fields exported by this module are fair game
for direct CLIF access.

## Reads in generated code, install at the host boundary

Generated code only ever *reads* the pinned register; it never installs one.
`set_pinned_reg` appears only in codegen tests — no production CLIF emits it.

Inside a function body, codegen reads the register through `CodegenFn::process_arg`
(`src/ir_codegen/fn_ctx.rs`), which emits one `get_pinned_reg(I64)` per block and
memoizes it. The register value is constant for the whole invocation, so keying
the memo by block keeps each use dominated by its definition without a cross-block
dominance argument. Runtime helper functions (BIFs) called from generated code
take the process as their leading argument; `call1_p` / `call_p` prepend
`process_arg()` to the BIF's args. (Halt-cont bodies and the static-closure
fetch read `get_pinned_reg` directly for the same purpose.)

Installing the register is the host's job. The Rust-side wrappers in
`runtime/src/pinned_abi.rs` — `call1` and `call2` — save the host's pinned
register, install the `Process*` the scheduler is dispatching, call the generated
entry, then restore the host's register before returning to Rust:

```text
save  host_pinned_reg            # spill to the stack
host_pinned_reg = process_ptr    # mov: now visible to generated code + BIF args
call  fz_entry(...)
restore host_pinned_reg          # reload from the stack
```

The save/restore is hand-written `asm!`, not Cranelift's `set_pinned_reg`. On x64
the host value is spilled to the stack (`mov [rsp], r15` / `mov r15, [rsp]`) and
the process is moved in with `mov`; on aarch64 it is `str x21` / `ldr x21` around
a `mov x21`. A portable fallback (other arches) calls the function directly and
cannot pin a process, so callers that need the register are unsupported there.

Because the wrapper preserves Rust's caller state at the boundary
(`clobber_abi("C")`) and restores the host register on return, the pinned register
survives ordinary runtime-helper calls made from within generated code — proven by
`pinned_register_survives_runtime_helper_call` in `clif_test.rs`.

## Entry coverage

The scheduler reaches generated fz code through exactly two SystemV→Tail-CC
shims, each entered through a `pinned_abi` wrapper so the register is set before
control transfers:

- `fz_resume(cont)` — the one re-entry verb, entered via `call1`. Whatever sits
  in `Process.runnable` (a continuation from a receive hit, after-timer fire, or
  mid-flight yield; or a fresh-task entry thunk, which is how a spawned task and
  `main` both start) is resumed through it. There is no separate main or spawn
  entry shim.
- `fz_drain_dtor_entry(closure, payload)` — entered via `call2`. It runs a
  resource destructor closure (generated fz code) under the process.

Both shims exist on the JIT path (`compiled.rs`, `src/exec/runtime.rs`) and the
AOT path (`runtime/src/aot_shim.rs`); the four call sites are the only users of
`pinned_abi::call1` / `call2`.

## Back-edge spending

With the base pinned, a loop back edge spends one reduction by touching
`reductions_remaining` directly through the register plus the ABI offset
(`emit_back_edge_yield_check` in `src/ir_codegen/terminator.rs`):

```text
p         = get_pinned_reg.i64
addr      = p + PROCESS_REDUCTIONS_REMAINING_OFFSET
remaining = load.i32  addr
remaining = remaining - 1
store        remaining, addr
brif remaining <= 0, yield, proceed
```

On the fast path it falls through to the normal tail call. On exhaustion it jumps
to a yield block that captures the next-iteration args into a scheduler-runnable
continuation and returns control to the scheduler.

`Process.reductions_remaining` and `Process.yield_reasons` are the sole authority
for the budget on every engine. See
[`reduction-yielding.md`](reduction-yielding.md) for how the budget is spent and
accounted.
