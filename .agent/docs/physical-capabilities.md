# Physical Capabilities

## Goal

Physical capabilities are compiler facts about private runtime objects. They
are not source values and must not affect semantic specialization.

Final form:

- semantic values carry program meaning;
- physical capabilities carry object-local permissions such as owned cons reuse;
- effect facts say when an operation allocates, observes allocation, is externally
  observable, reaches the scheduler, or halts;
- codegen consumes validated facts mechanically.

`src/ir_effects.rs` owns operation effect classification. Planner
return-context barriers and capability validation read that classifier instead
of carrying local publication rules.

## Current Model

The current owned-cons reuse implementation reaches the right allocation floor,
with these compiler facts:

- `src/fz_ir.rs` exposes `physical_capabilities` as the destination for
  object-local capabilities.
- `src/fz_ir.rs` exposes `physical_entry_params` only for entry slots that
  carry physical facts and are not semantic source values.
- `src/fz_ir.rs` keeps `ignored_entry_params` only for source wildcard holes.
- `src/ir_lower/cps.rs` transports `owned_cons_captures` through ordinary
  continuation capture machinery, but owned-cons source slots are physical
  params rather than ignored semantic params.
- `src/ir_dce.rs` owns capability liveness: live heads keep their source-cons
  params, dead heads drop their capabilities.
- `src/ir_capture_norm.rs` rewrites capture shapes and relies on DCE to preserve
  or drop capability payloads.
- `src/ir_codegen/support.rs` consumes physical capability facts with
  `emit_owned_cons_reuse_or_alloc`.

The standalone reuse-pruning pass and duplicate owned-cons capability lane
have been removed. Codegen reads reusable source objects from
`physical_capabilities`; semantic specialization ignores only the entry params
listed in `physical_entry_params`.

Spec dumps render `physical_capabilities` records so tests can assert the IR
facts directly instead of inferring them from backend text.

## Pinned Signal

Keep these floors green:

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
