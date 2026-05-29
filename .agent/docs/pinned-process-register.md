# Pinned Process Register

Generated code uses a Cranelift **pinned register** as the base pointer for the
current `Process`. This makes process switching for compiled code a single
base-pointer change rather than synchronizing a bundle of process-local mirror
cells, and it lets back edges spend the reduction budget by touching `Process`
fields directly.

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
process — there is no ambient thread-local. Runtime helper functions (BIFs)
called from generated code receive the process as their leading argument, which
codegen supplies by reading the pinned register (`get_pinned_reg`) at the call
site. Every scheduler-facing generated entry sets the pinned register to the
`Process*` the scheduler is dispatching, and restores the host's pinned register
before returning to Rust.

```text
save host_pinned_reg
host_pinned_reg = process_ptr        # for generated code + BIF args
call fz_entry(...)
restore host_pinned_reg
```

Because the wrapper preserves Rust's ABI at the boundary, the pinned register
survives ordinary runtime-helper calls made from within generated code. (The
old `CURRENT_PROCESS` thread-local was retired in fz-vdt — the process is now
threaded per call, never ambient, so two schedulers can be live at once.)

## Entry coverage

Every SystemV-to-tail shim that can start or resume fz code sets the pinned
register before transferring control: main entry, spawn entry, scheduler resume
closure entry, the AOT entry/shim equivalents, and the destructor-drain entry
when it runs generated fz code under a process.

## Back-edge spending

With the base pinned, a back edge reads, decrements, and stores
`reductions_remaining` through `get_pinned_reg` plus the ABI offset — no
process-independent reductions global is involved:

```text
p = get_pinned_reg.i64
remaining = load.i32  p + PROCESS_REDUCTIONS_REMAINING_OFFSET
remaining = remaining - back_edge_cost
store         remaining, p + PROCESS_REDUCTIONS_REMAINING_OFFSET
brgt remaining, 0, fast
```

`Process.reductions_remaining` and `Process.yield_reasons` are the sole
authority for the budget on every engine; the old compiled-only reductions
global and its thread-local mirror are gone. See
[`reduction-yielding.md`](reduction-yielding.md) for how the budget is spent and
accounted.
