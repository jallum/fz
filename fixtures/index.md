# Fixture index

Regenerated from README.md frontmatter by `cargo test fixture_index_up_to_date`.
Run with `BLESS=1` to rewrite after editing fixtures.

| fixture | purpose | paths |
|---------|---------|-------|
| `actor_ring/` | N-hop actor ring with self()-capture + spawn-with-captures + multi-clause CPS-split-in-body; closes fz-g8v by exercising the fz-qbg.2 multi-clause body cont-fn path end-to-end | jit, interp |
| `add1/` | smallest JIT round-trip — fn def + call + print | jit, interp, repl |
| `alias/` | nested-module path aliasing — `alias Long.Path` and `alias Long.Path, as: LP` | jit, interp, repl |
| `apply2/` | first-class fns — pass a fn into another fn and call it | jit, interp, repl |
| `ast_eval/` | tagged-tuple AST evaluator — first fixture to exercise multi-clause tuple-pattern dispatch end-to-end | jit, interp, aot, repl |
| `attributes/` | @moduledoc / @doc attributes parse and the module still executes | jit, interp, repl |
| `case_tuple_pattern_sequential/` | sequential calls returning tuple-pattern results (fz-i82 regression) | interp, jit, aot |
| `classify_two_clause/` | literal-vs-wildcard clause dispatch (`0` and `_`) | jit, interp, repl |
| `closure_typed_captures/` | fz-ul4.29.5 — closure dispatched via call_indirect through stub_fp | jit, interp, aot, repl |
| `cold_fn/` | minimal call site — one fn definition, one call, no scaffolding | jit, interp, repl |
| `concurrency_ping_pong/` | spawn + send + receive — parent blocks on receive, prints the message | jit, interp, aot |
| `cross_module_macro/` | defmacro in one module, called from another via `import Helpers, only: [twice: 1]` | jit, interp, repl |
| `curried_add/` | three-level currying — nested lambdas each capturing outer scope; exercises multi-depth closure allocation | jit, interp, aot, repl |
| `destructure_cons/` | refutable list-cons destructure on a statically-non-empty list — success-path parity for `[h | t] = xs` | jit, interp, aot, repl |
| `destructure_mixed/` | nested destructure mixing tuple arity and list cons — `{[h | t], y} = make()` across all four legs | jit, interp, aot, repl |
| `destructure_tuple/` | irrefutable tuple destructure in a let-style bind — first fixture to exercise `{a, b} = expr` across all four legs | jit, interp, aot, repl |
| `empty_list_distinct_from_nil/` | pin fz-s9y semantics — `nil` and `[]` print as distinct strings | jit, aot, interp, repl |
| `fib_tailrec/` | fibonacci via two-accumulator tail recursion — three-clause dispatch + tail-call forwarding under load | jit, interp, aot, repl |
| `file_handle/` | FileHandle = fd + libc::close dtor, exercising cstring/binary/integer marshal classes against real libc | jit, interp, aot |
| `file_resource_lifecycle/` | fz-swt.13 — File module wraps an fd in a resource; the dtor closes the fd at heap drop (interp/JIT/AOT parity). | interp, jit, aot |
| `fn_ref_ampersand/` | &name/arity parses as an explicit function reference, disambiguating overloaded names by arity | jit, interp |
| `hello/` | print each scalar shape — int, atom, bool, nil | jit, interp, repl |
| `higher_order/` | higher-order patterns — apply2, compose | jit, interp, aot, repl |
| `hot_fn/` | same call repeated — historical JIT tier-up trigger; today every call is JIT | jit, interp, repl |
| `if_constant_cond_with_call/` | fz-84m repro A — constant cond + non-tail call in if-arm; formerly panicked at fz_ir.rs:453 ('unknown block') because then-arm's CPS-split finalized the outer fn while else_b was still empty | jit, interp |
| `if_tail_call_in_arm_narrowed/` | fz-84m repro B — if-arm tail call + per-callsite narrowing; formerly silently dropped the tail-call (overwritten with Goto(join_b, [Var(0)])) | jit, interp |
| `if_tail_call_in_arm_unnarrowed/` | fz-84m repro C — same shape as repro B but with `n > 0` instead of `n == 0`, proving the bug was structural in lowering and NOT driven by per-callsite type narrowing | jit, interp |
| `import/` | selective import — `import Math, only: [add: 2]` | jit, interp, repl |
| `interp_only_main/` | tiny module with a single helper and a main — historical interp-tier-0 smoke test | jit, interp, repl |
| `list_primitives/` | list primitives from scratch — length / reverse / map / foldl exercising cons-pattern dispatch and first-class fns | jit, interp |
| `macro_inc/` | defmacro + quote/unquote round-trip — two macros, one nested in the other | jit, interp, repl |
| `modules/` | cross-module qualified calls — `M.double`, `M.quad`, `N.helper` | jit, interp, repl |
| `multi_caller_spec_divergent/` | fz-uwq.4 regression — divergent dispatch across two caller specs of the same higher-order fn | jit, interp, aot, repl |
| `multi_clause/` | multi-clause dispatch with a guard clause (`when n > 0`), plus recursive `fact` | jit, interp, repl |
| `multi_clause_body_with_call/` | minimal multi-clause Bug-2 repro — clause body has a Call. Pre-fz-qbg.2 panicked at fz_ir.rs:453; now lowers correctly via the per-clause body cont-fn path | jit, interp |
| `multi_relay/` | two workers both block on receive simultaneously; exercises scheduler managing multiple Blocked processes | jit, interp, aot |
| `mutual_recursion/` | mutual recursion — is_even/is_odd call each other; exercises cross-function recursive dispatch | jit, interp, aot, repl |
| `nested_modules/` | inner module addressed both fully-qualified (`Outer.Inner.f`) and via outer-local reference | jit, interp, repl |
| `polymorphic/` | parametric `id` exercised over int, atom, and bool | jit, interp, repl |
| `quicksort/` | closing fixture of the destructure-up-through-quicksort arc — `{lo, hi} = partition(...)` on the hot path of a recursive sort | jit, interp, aot, repl |
| `relay/` | one-hop relay — spawned child blocks on receive before parent sends; exercises non-blocking spawn + receive-parks semantics | jit, interp, aot |
| `resource_aot_dtor/` | AOT-compiled binary fires user-supplied resource dtors at heap drop | aot |
| `resource_lifecycle/` | fz-swt.12 — resource lifecycle (make_resource + .value + dtor) is observably identical across interp, JIT, AOT | interp, jit, aot |
| `sample_tests/` | `test()` macro from the prelude — assert_eq / assert_neq / assert | jit |
| `sample_tests_module/` | `test()` inside a defmodule body | jit |
| `shared_heap_send_large_bitstring/` | fz-cty.6 — sending a >64-byte bitstring via spawn-and-send rounds through ProcBin/SharedBin under JIT and AOT | jit, interp, aot |
| `spawn2_basic/` | fz-siu.12 — spawn/2 with min_heap_size hint behaves identically to spawn/1 | jit, interp, aot |
| `spawn_with_captures/` | fz-ul4.29.5 — spawn-with-captures lift (was forbidden v1) | jit, interp |
| `spec_boundary/` | fz-jg5.12 (RED.9) — @spec is a reduction boundary; fact has 1 body, not 0 | jit, interp |
| `spec_ok/` | fz-ul4.31.6 — declared @spec matches inferred behavior; | jit, interp, repl |
| `tail_recursion/` | 100k-deep self-recursion must TCO — exits cleanly with the accumulated count | jit, interp, aot |
| `tailcall_closure_captures/` | TailCallClosure with captured singleton closure-lit preserves narrow arg ABI through recursive HOF | jit, interp, aot, repl |
| `three_process_chain/` | two-hop process relay — main → first_relay → second_relay → main; exercises multi-process message chaining | jit, interp, aot |
| `type_dispatch/` | multi-clause fn dispatches on parameter type at runtime (fz-ty1.8/1.9) | interp, jit, aot |
| `vr1_int_arith/` | VR.1 — int-literal arithmetic elides the tag-check fast/slow path | jit, interp, repl |
| `vr2_float_arith/` | VR.2 — float-literal arithmetic + comparisons emit native fadd/fcmp, no dispatch | jit, interp, repl |
| `vr3_4_typed_capture/` | VR.3.4 / VR.4.3 — typed captures survive cont handoffs via native chain | jit, interp, repl |
| `vr3_float_args/` | VR.4 + VR.3.2 + .27.13 — narrow-spec float entry params arrive in F64 registers; fmul/fadd fire raw | jit, interp, repl |
| `vr3_int_args/` | VR.3.3 / VR.4.2.3 — typed int args flow through native ABI | jit, interp, repl |
| `vr4_2_native_call/` | VR.4.2 — leaf-bodied helper goes through the native ABI | jit, interp, repl |
| `vr5a_cross_kind_eq/` | VR.5a — cross-kind `==` folds to constant + emits type/dead-binop lint | jit, interp, repl |
| `vr5a_typed_eq/` | VR.5a — int-int / atom-atom equality lowers to a single icmp, no fz_value_eq dispatch | jit, interp, repl |
| `vr5b_typed_print/` | VR.5b — print dispatches to typed FFI when the arg Descr narrows | jit, interp, repl |
| `wildcard_then_specific/` | first-match-wins for wildcard-then-specific patterns (multi-clause fn and case) | jit, interp, aot, repl |
