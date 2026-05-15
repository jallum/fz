# Fixture index

Regenerated from README.md frontmatter by `cargo test fixture_index_up_to_date`.
Run with `BLESS=1` to rewrite after editing fixtures.

| fixture | purpose | paths |
|---------|---------|-------|
| `add1/` | smallest JIT round-trip — fn def + call + print | jit, interp |
| `alias/` | nested-module path aliasing — `alias Long.Path` and `alias Long.Path, as: LP` | jit, interp |
| `apply2/` | first-class fns — pass a fn into another fn and call it | jit, interp |
| `attributes/` | @moduledoc / @doc attributes parse and the module still executes | jit, interp |
| `classify_two_clause/` | literal-vs-wildcard clause dispatch (`0` and `_`) | jit, interp |
| `closure_typed_captures/` | fz-ul4.29.5 — closure dispatched via call_indirect through stub_fp | jit, interp, aot |
| `cold_fn/` | minimal call site — one fn definition, one call, no scaffolding | jit, interp |
| `concurrency_ping_pong/` | spawn + send + receive — parent blocks on receive, prints the message | jit, interp, aot |
| `cross_module_macro/` | defmacro in one module, called from another via `import Helpers, only: [twice: 1]` | jit, interp |
| `curried_add/` | three-level currying — nested lambdas each capturing outer scope; exercises multi-depth closure allocation | jit, interp, aot |
| `fib_tailrec/` | fibonacci via two-accumulator tail recursion — three-clause dispatch + tail-call forwarding under load | jit, interp, aot |
| `hello/` | print each scalar shape — int, atom, bool, nil | jit, interp |
| `higher_order/` | higher-order patterns — apply2, compose | jit, interp, aot |
| `hot_fn/` | same call repeated — historical JIT tier-up trigger; today every call is JIT | jit, interp |
| `import/` | selective import — `import Math, only: [add: 2]` | jit, interp |
| `interp_only_main/` | tiny module with a single helper and a main — historical interp-tier-0 smoke test | jit, interp |
| `macro_inc/` | defmacro + quote/unquote round-trip — two macros, one nested in the other | jit, interp |
| `modules/` | cross-module qualified calls — `M.double`, `M.quad`, `N.helper` | jit, interp |
| `multi_clause/` | multi-clause dispatch with a guard clause (`when n > 0`), plus recursive `fact` | jit, interp |
| `mutual_recursion/` | mutual recursion — is_even/is_odd call each other; exercises cross-function recursive dispatch | jit, interp, aot |
| `nested_modules/` | inner module addressed both fully-qualified (`Outer.Inner.f`) and via outer-local reference | jit, interp |
| `polymorphic/` | parametric `id` exercised over int, atom, and bool | jit, interp |
| `sample_tests/` | `test()` macro from the prelude — assert_eq / assert_neq / assert | jit |
| `sample_tests_module/` | `test()` inside a defmodule body | jit |
| `spawn2_basic/` | fz-siu.12 — spawn/2 with min_heap_size hint behaves identically to spawn/1 | jit, interp, aot |
| `spawn_with_captures/` | fz-ul4.29.5 — spawn-with-captures lift (was forbidden v1) | jit, interp |
| `spec_ok/` | fz-ul4.31.6 — declared @spec matches inferred behavior; | jit, interp |
| `tail_recursion/` | 100k-deep self-recursion must TCO — exits cleanly with the accumulated count | jit, interp, aot |
| `three_process_chain/` | two-hop process relay — main → first_relay → second_relay → main; exercises multi-process message chaining | jit |
| `vr1_int_arith/` | VR.1 — int-literal arithmetic elides the tag-check fast/slow path | jit, interp |
| `vr2_float_arith/` | VR.2 — float-literal arithmetic + comparisons emit native fadd/fcmp, no dispatch | jit, interp |
| `vr3_4_typed_capture/` | VR.3.4 / VR.4.3 — typed captures survive cont handoffs via native chain | jit, interp |
| `vr3_float_args/` | VR.4 + VR.3.2 + .27.13 — narrow-spec float entry params arrive in F64 registers; fmul/fadd fire raw | jit, interp |
| `vr3_int_args/` | VR.3.3 / VR.4.2.3 — typed int args flow through native ABI | jit, interp |
| `vr4_2_native_call/` | VR.4.2 — leaf-bodied helper goes through the native ABI | jit, interp |
| `vr5a_cross_kind_eq/` | VR.5a — cross-kind `==` folds to constant + emits type/dead-binop lint | jit, interp |
| `vr5a_typed_eq/` | VR.5a — int-int / atom-atom equality lowers to a single icmp, no fz_value_eq dispatch | jit, interp |
| `vr5b_typed_print/` | VR.5b — print dispatches to typed FFI when the arg Descr narrows | jit, interp |
