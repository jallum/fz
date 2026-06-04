# Control-Flow Lowering

`if`, `case`, `cond`, `with`, and `receive` lower into ordinary IR functions
connected by tail calls. The IR has no nested-block "join" terminator, so a
branching construct cannot keep a meeting point inside its own function: any
non-tail call in an arm CPS-splits the current function (see `cps_split_call`),
finalizes it, and would strand that meeting point in a built, immutable `FnIr`.
The fix is to make every arm body, and the post-construct meeting point, its own
**continuation function**. Arm-internal CPS-splits then stay confined to that
arm's lineage and never finalize the construct's outer function early.

The pieces a reader needs:

- **`ContFn`** (`cps.rs`) — a handle to a freshly minted continuation function:
  a `FnId`, a name, an `FnCategory`, and `outer_captured` (the visible locals
  snapshotted at mint time, by name + outer `Var`). The builder is created
  lazily; the captured names become the function's entry params after any
  extras.
- **Three helpers** in `cps.rs` do all the wiring:
  - `mint_cont_fn` allocates the `FnId` and snapshots the outer env.
  - `switch_to_cont_fn(cont, extra_param_count)` finalizes the current
    function, starts the cont's builder with params `[extras…, captured…]`,
    rebinds the env from captured names to the new param `Var`s, and returns the
    extra params.
  - `finalize_arm(arm_value, join)` emits the terminator that ends an arm body.
- **The outer function** owns selecting which arm runs.
- **Each arm function** owns evaluating one source arm.
- **The join function** (present only when the construct is non-tail) owns
  receiving the arm value and continuing the surrounding code.

Control-flow continuation functions carry `FnCategory::ControlFlowCont` and are
named after their construct: `if_then` / `if_else` / `if_join`,
`case_clause_N` / `case_join`, `cond_arm_N` / `cond_fail` / `cond_join`,
`with_else_N` / `with_fail` / `with_join`, and `rx_clause_N_body` /
`rx_clause_N_guard` / `rx_after_body` / `receive_join`. Multi-clause function
bodies (`fn_clause_N`) use `FnCategory::MultiClauseCont`; CPS continuations
(`k_N`) use `FnCategory::CpsCont`.

## How each construct is shaped

The lowering entry points live in `expr.rs` (`lower_case`, `lower_cond`,
`lower_with`), `cond.rs` (`lower_if`, `lower_multi_clause`), and `receive.rs`
(`lower_receive`). They share the helpers above and differ only in how the outer
function reaches an arm.

`if` (`cond.rs` `lower_if`) lowers the condition, mints `if_then` / `if_else`
(and `if_join` when non-tail), and ends the outer block with `Term::If`. Each
arm block `Term::TailCall`s its arm function with the outer captures. The arm
function lowers its body, then `finalize_arm` ends it.

`case` (`expr.rs` `lower_case`) lowers the subject, then compiles a
`PatternMatrix` into the outer function via `lower_pattern_matrix_to_current_fn`.
The matrix dispatch tail-calls a per-clause `case_clause_N` function with the
post-match env (outer captures plus the clause's pattern bindings). A final
mismatch routes to a `fail_block` that `Term::Halt`s the atom `case_clause`.
`with`'s else branch and multi-clause function dispatch use the same
matrix-into-current-function pattern, halting `with_clause` / `function_clause`.

`cond` (`expr.rs` `lower_cond`) mints one `cond_arm_N` per arm plus a
`cond_fail`. The outer function tail-calls the first arm; each arm function
lowers its own test, branches with `Term::If` to a body block or a fall block,
and the fall block tail-calls the next arm (or `cond_fail`, which halts
`cond_clause`). Wrapping the whole arm — test included — in its own function is
what keeps a non-tail call *in the test* from finalizing the outer function.

`with` (`expr.rs` `lower_with`) walks its bindings inline in the outer function.
Each `Match` binding gets a `mismatch_b` block that tail-calls `with_fail`
carrying the unmatched value plus captures. The main body lowers inline and is
ended by `finalize_arm`. `with_fail` receives the unmatched value as its extra
param and either halts `with_clause` (no `else`) or dispatches the else clauses
through the matrix to `with_else_N` bodies.

`receive` (`receive.rs` `lower_receive`) is matcher-driven: the outer function's
block ends with `Term::ReceiveMatched`, whose `clauses` name the body and guard
`FnId`s and whose `matcher` is the cached `Arc<Matcher>`. Bodies (`rx_clause_N_
body`), guards (`rx_clause_N_guard`), and the optional `rx_after_body` are
continuation functions reached by `switch_to_cont_fn`. Each body's params are
its pattern's bound names followed by the shared captures; `finalize_arm` ends
each body the same way the other constructs do. (The matcher ABI itself is
documented separately.)

## Tailness across the construct boundary

The join is part of the source expression, so an arm is in true tail position
only when the whole construct is. Every construct computes this the same way:

```text
arm_is_tail = join_opt.is_none()
```

`join_opt` is `Some` exactly when the construct is non-tail (`is_tail` is
false), i.e. its value feeds surrounding code. In that case the arm body is
lowered with `is_tail = false`, and `finalize_arm` ends it with
`Term::TailCall(join.id, [arm_value, …captured])`. When the construct is in tail
position there is no join; arms are lowered with `is_tail = true` and
`finalize_arm` ends them with `Term::Return(arm_value)`. If an arm already
self-terminated (its own `Return` / `Halt` / inner `TailCall`),
`finalize_arm` emits nothing.

The observable contract: the join function takes the arm value as its single
extra param. `switch_to_cont_fn(join, 1)` returns that param, and the construct's
lowering returns it as the construct's value, so the surrounding code lowers
*into the join function* with the value in hand.

This is why a call inside a non-tail arm must be treated as non-tail: its result
has to flow to the join, not return from the arm. Because `arm_is_tail` is
derived from `join_opt`, this falls out of the model rather than being a
special case.

## Walkthrough

```fz
next = if rem(index, nth) == 0, do: fun.(head), else: head
[next | rest]
```

The `if` is the right-hand side of a `Match`, so it lowers non-tail and
`join_opt` is `Some(if_join)`. `fun.(head)` is a non-tail closure call inside
`if_then`; it CPS-splits that arm's lineage and produces a value, then
`finalize_arm` tail-calls `if_join` with `[that_value, …captures]`.
`if_join`'s extra param is the `if`'s value. `lower_if` returns it, the `Match`
binds `next` to it, and `[next | rest]` lowers inside `if_join`.

Had the `if` been in tail position, `if_then` would have returned `fun.(head)`'s
value directly, with no `if_join`.

## Tests

The structural tests in `ir_lower_test.rs` show each construct's function names:
`lower_if_uses_continuation_fns`, `lower_case_uses_per_clause_cont_fns`,
`lower_cond_uses_per_arm_cont_fns`, `lower_with_uses_continuation_fns`, and the
non-tail variants `lower_if_nontail_uses_join_fn`. The end-to-end tests
`non_tail_if_call_arm_flows_through_join` (and its `case`/`cond` siblings) prove
a non-tail call in an arm reaches the join instead of returning past the
surrounding code; the `fz_84m_repro_*` tests cover constant-condition and
tail-call-in-arm cases running end to end.
</content>
</invoke>
