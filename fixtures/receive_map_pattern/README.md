---
purpose: "receive with map pattern (atom key) — locks PerRow Map three-path parity"
paths: [jit, interp, aot]
budget.codegen.functions: 19
budget.codegen.instructions: 399
budget.specs.count: 8
budget.typer.worklist_pops: 18
budget.typer.walk_calls: 18
budget.typer.type_fn_calls: 8
budget.typer.matcher_specs: 0
budget.typer.vars: 58
budget.typer.blocks: 10
budget.typer.stmts: 31
budget.typer.dispatches: 1
---

# receive_map_pattern

fz-puj.47 (X6) — receive matcher implementing Pattern::Map via PerRow.

Map patterns route through PerRow (no Switch specialisation), so the
matcher dispatches via `fz_matcher_map_get(map, key) -> u64` per entry.
A NIL_BITS return signals miss; otherwise the lookup result recurses
through compile_pattern against the value pattern.

This fixture uses `%{name: n}` against incoming maps; the value
position binds `n` to the atom under the `name` key. Interp mirrors
via direct heap-walk of the map's pair array.

Float and Binary map-key patterns surface a clean CodegenError pointing
at a follow-up — encoding them would require a per-receive startup
allocation pass (heap-typed RHS).
