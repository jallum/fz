# Physical Capabilities

## Goal

Physical capabilities are compiler facts about private runtime objects. They
are not source values and must not affect semantic specialization.

Final form:

- semantic values carry program meaning;
- physical capabilities carry object-local permissions such as owned cons reuse;
- effect facts say when an operation publishes, observes allocation, deep-copies,
  or crosses a scheduler/materialization boundary;
- codegen consumes validated facts mechanically.

`src/ir_effects.rs` owns operation effect classification. Reuse pruning,
planner return-context barriers, and future capability validation should read
that classifier instead of carrying local publication rules.

## Current Scaffold

The current owned-cons reuse implementation reaches the right allocation floor,
but it still uses transitional plumbing:

- `src/fz_ir.rs` exposes `physical_entry_params` as the destination for
  object-local capabilities.
- `src/fz_ir.rs` stores `ignored_entry_params` beside semantic params.
- `src/fz_ir.rs` stores `owned_cons_reuse_credits` as the reusable-cons seed.
- `src/ir_lower/cps.rs` transports `owned_cons_captures` through ordinary
  continuation capture machinery.
- `src/ir_capture_norm.rs` runs local DCE to repair capability liveness after
  capture pruning.
- `src/ir_reuse.rs` performs a standalone publication-pruning cleanup pass
  driven by `src/ir_effects.rs`.
- `src/ir_codegen/support.rs` consumes the remaining credits with
  `emit_owned_cons_reuse_or_alloc`.

These are removal targets. They are acceptable only while the IR lacks a
separate physical capability lane and structured effect facts.

## Pinned Signal

Keep these floors green while removing the scaffold:

```text
quicksort native:
  list_cons_allocs = 11
  closure_allocs = 0

enum_list_allocations native:
  list_cons_allocs = 5
  closure_allocs = 0

enum_reduce_suspend native:
  closure_allocs = 1
```

## Rule

Do not repair the model in codegen. Lowering records provenance, effect
classification validates it, DCE/capture normalization preserves or drops it,
and codegen lowers what remains.
