# Fixture index

Regenerated from header comments by `cargo test fixture_index_up_to_date`.
Run with `BLESS=1` to rewrite after editing fixtures.

| file | purpose | paths |
|------|---------|-------|
| `add1.fz` | smallest JIT round-trip — fn def + call + print | jit, interp |
| `alias.fz` | nested-module path aliasing — `alias Long.Path` and `alias Long.Path, as: LP` | jit, interp |
| `apply2.fz` | first-class fns — pass a fn into another fn and call it | jit, interp |
| `attributes.fz` | @moduledoc / @doc attributes parse and the module still executes | jit, interp |
| `classify_two_clause.fz` | literal-vs-wildcard clause dispatch (`0` and `_`) | jit, interp |
| `cold_fn.fz` | minimal call site — one fn definition, one call, no scaffolding | jit, interp |
| `concurrency_ping_pong.fz` | spawn + send + receive — parent blocks on receive, child sends 42, main returns 42 | jit |
| `cross_module_macro.fz` | defmacro in one module, called from another via `import Helpers, only: [twice: 1]` | jit, interp |
| `hello.fz` | print each scalar shape — int, atom, bool, nil | jit, interp |
| `higher_order.fz` | higher-order patterns — apply2, compose | jit, interp |
| `hot_fn.fz` | same call repeated — historical JIT tier-up trigger; today every call is JIT | jit, interp |
| `id_int_atom.fz` | identity fn over int and atom — no type-driven specialization | jit, interp |
| `import.fz` | selective import — `import Math, only: [add: 2]` | jit, interp |
| `interp_only_main.fz` | tiny module with a single helper and a main — historical interp-tier-0 smoke test | jit, interp |
| `macro_inc.fz` | defmacro + quote/unquote round-trip — two macros, one nested in the other | jit, interp |
| `modules.fz` | cross-module qualified calls — `M.double`, `M.quad`, `N.helper` | jit, interp |
| `multi_clause.fz` | multi-clause dispatch with a guard, plus recursive `fact` — currently deferred on `# paths: ` because guard lowering is not yet wired | _(deferred: fz-ul4.24 (guard clauses in ir_lower))_ |
| `nested_modules.fz` | inner module addressed both fully-qualified (`Outer.Inner.f`) and via outer-local reference | jit, interp |
| `polymorphic.fz` | parametric `id` exercised over int, atom, and bool | jit, interp |
| `sample_tests.fz` | `test()` macro from the prelude — assert_eq / assert_neq / assert | jit |
| `sample_tests_module.fz` | `test()` inside a defmodule body | jit |
| `tail_recursion.fz` | 100k-deep self-recursion must TCO — exits cleanly with the accumulated count | jit |
