# Fixture index

Regenerated from header comments by `cargo test fixture_index_up_to_date`.
Run with `BLESS=1` to rewrite after editing fixtures.

| file | purpose | paths |
|------|---------|-------|
| `add1.fz` | smallest JIT round-trip — fn def + call + print | jit, interp |
| `alias.fz` | nested-module path aliasing — `alias Long.Path` and `alias Long.Path, as: LP` | jit, interp |
| `apply2.fz` | first-class fns — pass a fn into another fn and call it | jit, interp |
| `attributes.fz` | @moduledoc / @doc attributes parse and the module still executes | jit, interp |
| `callsite_narrowing_dist.fz` | fz-ul4.27.10 — call-site arg narrowing flows caller arg types into callee entry params | jit, interp |
| `classify_two_clause.fz` | literal-vs-wildcard clause dispatch (`0` and `_`) | jit, interp |
| `closure_typed_captures.fz` | fz-ul4.29.5 — closure dispatched via call_indirect through stub_fp | jit, interp |
| `cold_fn.fz` | minimal call site — one fn definition, one call, no scaffolding | jit, interp |
| `concurrency_ping_pong.fz` | spawn + send + receive — parent blocks on receive, prints the message | jit, interp |
| `cross_module_macro.fz` | defmacro in one module, called from another via `import Helpers, only: [twice: 1]` | jit, interp |
| `expect_clif_demo.fz` | demonstrate expect_clif_contains / expect_clif_excludes header keys (fz-ul4.27.1) | jit, interp |
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
| `spawn_with_captures.fz` | fz-ul4.29.5 — spawn-with-captures lift (was forbidden v1) | jit, interp |
| `spec_ok.fz` | fz-ul4.31.6 — declared @spec matches inferred behavior; | jit, interp |
| `tail_recursion.fz` | 100k-deep self-recursion must TCO — exits cleanly with the accumulated count | jit, interp |
| `vr1_int_arith.fz` | VR.1 — int-literal arithmetic elides the tag-check fast/slow path | jit, interp |
| `vr2_float_arith.fz` | VR.2 — float-literal arithmetic + comparisons emit native fadd/fcmp, no dispatch | jit, interp |
| `vr3_4_typed_capture.fz` | VR.3.4 / VR.4.3 — typed captures survive cont handoffs via native chain | jit, interp |
| `vr3_float_args.fz` | VR.4 + VR.3.2 + .27.13 — narrow-spec float entry params arrive in F64 registers; fmul/fadd fire raw | jit, interp |
| `vr3_int_args.fz` | VR.3.3 / VR.4.2.3 — typed int args flow through native ABI | jit, interp |
| `vr4_2_native_call.fz` | VR.4.2 — leaf-bodied helper goes through the native ABI | jit, interp |
| `vr5a_cross_kind_eq.fz` | VR.5a — cross-kind `==` folds to constant + emits type/dead-binop lint | jit, interp |
| `vr5a_typed_eq.fz` | VR.5a — int-int / atom-atom equality lowers to a single icmp, no fz_value_eq dispatch | jit, interp |
| `vr5b_typed_print.fz` | VR.5b — print dispatches to typed FFI when the arg Descr narrows | jit, interp |
