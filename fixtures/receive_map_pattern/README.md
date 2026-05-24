---
purpose: "receive with map pattern (atom key) — locks PerRow Map three-path parity"
paths: [jit, interp, aot]
budget.codegen.functions: 15
budget.codegen.instructions: 1091
budget.specs.count: 12
budget.typer.worklist_pops: 30
budget.typer.walk_calls: 30
budget.typer.type_fn_calls: 12
budget.typer.matcher_specs: 0
budget.typer.vars: 64
budget.typer.blocks: 14
budget.typer.stmts: 31
budget.typer.dispatches: 5
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
