# IR Planner Rename

## Goal

Rename the compiler phase currently exposed as `ir_typer` so the phase name
matches its actual contract: produce the typed execution plan consumed by
later IR passes and codegen.

## Final Names

Use these names for the rename:

- Rust module: `ir_typer` -> `ir_planner`
- Top-level phase API: `type_module` -> `plan_module`
- Per-module product: `ModuleTypes` -> `ModulePlan`
- Per-specialization product: `FnTypes` -> `SpecPlan`
- User/agent doc: `dispatch-as-typer-output.md` -> `dispatch-as-planner-output.md`
- Telemetry event: `fz.typer.typed` -> `fz.planner.planned`
- Fixture budget keys: `budget.typer.*` -> `budget.planner.*`

## Boundary

The rename is for the phase boundary and its aggregate planning products.
Keep type-specific vocabulary where the code is literally type inference:

- `type_fn`
- `TYPE_FN_CALLS`
- `vars`
- `block_envs`
- `Ty`
- narrowing helpers and concrete type helpers

`SpecPlan` is intentionally broader than a type map. It owns Var and block-env
types, dispatch choices, return-use facts, return-context plans, reachable
blocks, dead-branch facts, and function-constant facts for one specialization.

`ModulePlan` is intentionally broader than module-wide type information. It
owns specialization plans, effective returns, any-key indexes, precedence,
effect summaries, SCC facts, cross-spec dead branches, and closure handles.

## Compatibility

Do not keep a compatibility shim for the old telemetry or fixture budget names.
The fixture README files and tests are in-repo consumers, so the rename should
move the public surface to planner vocabulary in one ticket.

## Non-Goals

Do not change planner behavior, dispatch semantics, return-demand semantics,
or codegen lowering as part of the rename. Do not flatten local type-inference
terminology into planner terminology when the narrower word is still correct.
