---
purpose: "&name/arity parses as an explicit function reference, disambiguating overloaded names by arity"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 18
budget.specs.count: 6
budget.planner.worklist_pops: 9
budget.planner.walk_calls: 9
budget.planner.type_fn_calls: 6
budget.planner.matcher_specs: 0
budget.planner.vars: 37
budget.planner.blocks: 9
budget.planner.stmts: 21
budget.planner.dispatches: 2
---

# fn_ref_ampersand

fz-swt.5 — Elixir-style `&name/arity` syntax for first-class function
references. Today a bare name lowered to a zero-capture closure picks
"first defined wins" for overloaded names; `&pick/1` vs `&pick/2` makes
that choice explicit.
