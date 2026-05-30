# Pinned Process Register

Generated code uses a Cranelift **pinned register** as the base pointer for the
current `Process`. This makes process switching for compiled code a single
base-pointer change, and it lets back edges spend the reduction budget by
touching `Process` fields directly.

## The register

`enable_pinned_reg` is set on both the JIT and AOT ISA builders. With it enabled,
CLIF may use `get_pinned_reg` / `set_pinned_reg`, and Cranelift removes the
register from normal allocation. The register is architecture-selected, not
caller-selected:

- x64: `r15`
- aarch64: `x21`

## Process ABI surface

Codegen depends on a small, explicit offset contract — never on the whole Rust
`Process` layout. `runtime/src/process_abi.rs` owns it:

```rust
pub const PROCESS_REDUCTIONS_REMAINING_OFFSET: i32 =
    std::mem::offset_of!(Process, reductions_remaining) as i32;
pub const PROCESS_YIELD_REASONS_OFFSET: i32 =
    std::mem::offset_of!(Process, yield_reasons) as i32;
```

Each offset has a test asserting it equals the field's real offset in `Process`.
Only fields listed in this module are fair game for direct CLIF access.

## Sole process handle for compiled code

The pinned register is the **only** way generated code names the running
process: it never reads an ambient thread-local to find the process. (The
scheduler does keep a libdispatch-style per-worker thread-local recording which
task each worker currently owns — see `runtime/src/process.rs` — but that is
ownership bookkeeping the generated code never consults.) Runtime helper
functions (BIFs)
called from generated code receive the process as their leading argument, which
codegen supplies by reading the pinned register (`get_pinned_reg`) at the call
site. Generated code only ever *reads* the pinned register; installing it is the
host's job. The Rust-side wrappers in `runtime/src/pinned_abi.rs` (`call1` /
`call2`) save the host's pinned register, install the `Process*` the scheduler is
dispatching, call the generated entry, then restore the host's register before
returning to Rust. The install/restore is hand-written `asm!` — `mov`/`str` of
the architecture's pinned register — not Cranelift's `set_pinned_reg`.

```text
save host_pinned_reg
host_pinned_reg = process_ptr        # for generated code + BIF args
call fz_entry(...)
restore host_pinned_reg
```

Because the wrapper preserves Rust's ABI at the boundary, the pinned register
survives ordinary runtime-helper calls made from within generated code.
Threading the process per call, never through an ambient global, is what lets
two schedulers run live on one worker at once.

## Entry coverage

Every SystemV-to-tail shim that can start or resume fz code is invoked through a
`pinned_abi` wrapper that installs the pinned register before transferring
control: main entry (`fz_main_entry`), spawn entry (`fz_spawn_entry`), scheduler
resume (`fz_resume`), the AOT shim equivalents in `runtime/src/aot_shim.rs`, and
the destructor-drain entry (`fz_drain_dtor_entry`) when it runs generated fz code
under a process.

## Back-edge spending

With the base pinned, a back edge reads, decrements by one, and stores
`reductions_remaining` through `get_pinned_reg` plus the ABI offset
(`emit_back_edge_yield_check` in `src/ir_codegen/terminator.rs`):

```text
p = get_pinned_reg.i64
remaining = load.i32  p + PROCESS_REDUCTIONS_REMAINING_OFFSET
remaining = remaining - 1
store         remaining, p + PROCESS_REDUCTIONS_REMAINING_OFFSET
brif remaining <= 0, yield, fast
```

`Process.reductions_remaining` and `Process.yield_reasons` are the sole
authority for the budget on every engine. See
[`reduction-yielding.md`](reduction-yielding.md) for how the budget is spent and
accounted.
