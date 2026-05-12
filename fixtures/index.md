# Fixture index

Regenerated from header comments by `cargo test fixture_index_up_to_date`.
Run with `BLESS=1` to rewrite after editing fixtures.

| file | purpose | paths |
|------|---------|-------|
| `add1.fz` | smallest JIT round-trip — fn def + call + print | jit, interp, aot |
| `alias.fz` | nested-module path aliasing — `alias Long.Path` and `alias Long.Path, as: LP` | jit, interp, aot |
| `apply2.fz` | first-class fns — pass a fn into another fn and call it | jit, interp, aot |
| `attributes.fz` | @moduledoc / @doc attributes parse and the module still executes | jit, interp, aot |
| `callsite_narrowing_dist.fz` | fz-ul4.27.10 — call-site arg narrowing flows caller arg types into callee entry params | jit, interp, aot |
| `classify_two_clause.fz` | literal-vs-wildcard clause dispatch (`0` and `_`) | jit, interp, aot |
| `cold_fn.fz` | minimal call site — one fn definition, one call, no scaffolding | jit, interp, aot |
| `concurrency_ping_pong.fz` | spawn + send + receive — parent blocks on receive, prints the message | jit, interp, aot |
| `cross_module_macro.fz` | defmacro in one module, called from another via `import Helpers, only: [twice: 1]` | jit, interp, aot |
| `expect_clif_demo.fz` | demonstrate expect_clif_contains / expect_clif_excludes header keys (fz-ul4.27.1) | jit, interp, aot |
| `hello.fz` | print each scalar shape — int, atom, bool, nil | jit, interp, aot |
| `higher_order.fz` | higher-order patterns — apply2, compose | jit, interp, aot |
| `hot_fn.fz` | same call repeated — historical JIT tier-up trigger; today every call is JIT | jit, interp, aot |
| `id_int_atom.fz` | identity fn over int and atom — no type-driven specialization | jit, interp, aot |
| `import.fz` | selective import — `import Math, only: [add: 2]` | jit, interp, aot |
| `interp_only_main.fz` | tiny module with a single helper and a main — historical interp-tier-0 smoke test | jit, interp, aot |
| `macro_inc.fz` | defmacro + quote/unquote round-trip — two macros, one nested in the other | jit, interp, aot |
| `modules.fz` | cross-module qualified calls — `M.double`, `M.quad`, `N.helper` | jit, interp, aot |
| `multi_clause.fz` | multi-clause dispatch with a guard, plus recursive `fact` — currently deferred on `# paths: ` because guard lowering is not yet wired | _(deferred: fz-ul4.24 (guard clauses in ir_lower))_ |
| `nested_modules.fz` | inner module addressed both fully-qualified (`Outer.Inner.f`) and via outer-local reference | jit, interp, aot |
| `polymorphic.fz` | parametric `id` exercised over int, atom, and bool | jit, interp, aot |
| `sample_tests.fz` | `test()` macro from the prelude — assert_eq / assert_neq / assert | jit |
| `sample_tests_module.fz` | `test()` inside a defmodule body | jit |
| `tail_recursion.fz` | 100k-deep self-recursion must TCO — exits cleanly with the accumulated count | jit, interp, aot |
| `vr1_int_arith.fz` | VR.1 — int-literal arithmetic elides the tag-check fast/slow path | jit, interp, aot |
| `vr2_float_arith.fz` | VR.2 — float-literal arithmetic + comparisons emit native fadd/fcmp, no dispatch | jit, interp, aot |
| `vr3_float_args.fz` | VR.3.2 — typed float entry-frame slots flow raw f64 across multiple ops in one block | jit, interp, aot |
| `vr5a_cross_kind_eq.fz` | VR.5a — cross-kind `==` folds to constant + emits type/dead-binop lint | jit, interp, aot |
| `vr5a_typed_eq.fz` | VR.5a — int-int / atom-atom equality lowers to a single icmp, no fz_value_eq dispatch | jit, interp, aot |
