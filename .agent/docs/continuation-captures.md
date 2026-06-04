# Continuation Captures

## Model

A continuation capture is dataflow, not scope. Scope decides what names the
lowerer can look up; the capture set decides what values the continuation body
actually reads when it resumes. A variable does not belong in a continuation
just because it was visible when the continuation was created.

Lowering splits source expressions into CPS continuations and emits a
conservative capture candidate for each — every name visible at the split point.
`ir_capture_norm` is the boundary that turns those candidates into the ABI:

```text
continuation captures = the caller Vars whose entry param the body actually reads
```

After the pass, no continuation carries an unread capture. The single-call-site
and receive-matched paths additionally collapse a caller `Var` captured into
several positions to a single entry param; the shared-call-site and tail-call
paths prune dead positions only and may keep the same caller `Var` in two live
positions.

The capture set is independent of how the continuation is represented at
runtime. A compiler-known native continuation can carry these same captures in a
stack-backed lazy descriptor and only become a heap closure when a scheduler
boundary needs one (see
[`lazy-continuation-materialization.md`](lazy-continuation-materialization.md)).
The shape this pass computes is the same either way.

## What The Pass Owns

`ir_capture_norm` normalizes the capture/argument shape at four kinds of
continuation site, each keyed by the `FnIr` it resumes:

- `Term::Call` and `Term::CallClosure` continuations (a `Cont { fn_id, captured }`
  carried on the call terminator).
- tail-call continuation joins — a `Term::TailCall` whose `callee` is a
  `ControlFlowCont` or `MultiClauseCont` and is not a back edge.
- `Term::ReceiveMatched` shared captures threaded into every clause body, clause
  guard, and the optional `after` body.

It runs as the last step of lowering, right after `erase_brands`, so the
planner, codegen, and interpreter all see one settled continuation ABI.

The pass owns two distinct decisions:

- **pruning** — a captured position whose entry param the body never reads is
  removed from the continuation entry, from every call edge, and from any
  physical payload.
- **dedup** — when one caller `Var` is captured into several positions, the
  surviving positions collapse to a single entry param, and the body is
  rewritten so the dropped params point at the representative.

Pruning and dedup are decided per site against `live_vars_after_local_dce`,
which clones the continuation `FnIr`, runs ordinary DCE on the clone, and asks
which entry params remain used. Each fix is applied immediately and the whole
walk repeats until no site changes, so a prune that exposes more dead params is
caught on the next pass.

The single-call-site path and the receive-matched path both prune and dedup. The
shared-call-site path and the tail-call path prune only: they keep a common entry
shape across every caller, so they drop the positions dead in the body but leave
duplicate captures alone.

### Shared continuation sites

When several call terminators resume the same continuation `FnId`, they must keep
identical entry shapes. The pass treats them as one unit: it computes the set of
entry params the body reads, then removes exactly those dead positions from every
edge. The continuation entry params and each caller's `captured` list stay in
lockstep.

### Tail-call joins

A control-flow or multi-clause join is reached by `Term::TailCall` from each
branch with the same arg arity as the join's entry params. The pass drops the
positions the join body never reads from the join entry and from every caller's
args. It also carries the surviving entries' `ignored_entry_params` flags
forward, so a join param that is intentionally unbound stays marked after the
reshape.

### Owned-cons reuse and physical liveness

An owned-cons reuse capability is a physical fact, not an ordinary value. A
continuation entry param can be the live head of a cons cell whose source cell
codegen still needs in order to reuse storage. Local DCE may drop the source
cell because no source expression reads it again.

`ir_dce` keeps that source alive on physical grounds: `collect_used` adds a
capability's `source` to the used set whenever its `head` is semantically used,
and `prune_dead_owned_cons_capabilities` drops the capability, its
`physical_entry_params` entry, and the source projection when the head is not.
`ir_capture_norm` rewrites the capture shape and then runs that same DCE; it has
no separate owned-cons repair path. When it does dedup, it rewrites
`physical_entry_params` and `physical_capabilities` through the substitution so
the physical facts track the surviving params.

## Lambda Captures

Lambda lowering uses the same idea one step earlier. A lambda captures the free
names of its body, found by `lambda_free_names`, intersected with the locals
visible where the lambda is written — not every visible local.

```text
fn outer(x, y), do: fn(z) -> x + z
```

The lambda's body reads `x` and `z`. `z` is a lambda param, so the only capture
is `x`; `y` is visible but unread and never enters the closure.

## Telemetry

Each site that changes emits `fz.ir.capture_norm.captures_pruned`. The
`producer` metadata names the site kind (`call_continuation`,
`shared_call_continuation`, `tail_call_continuation`, or `receive_matched`), and
the measurements report the reshape:

```text
fz.ir.capture_norm.captures_pruned
  before_captures: 2
  after_captures:  1
  pruned_captures: 1
```

The single-call-site and receive-matched events also carry
`deduplicated_captures` (how many duplicate positions collapsed); the shared and
tail-call events carry `caller_count`; receive-matched also carries
`outcome_count`.

## Tests

The telemetry event proves the pass made a decision; structural assertions on
the rewritten IR prove it made the right one. A test reads back the continuation
entry params, the call-edge `captured` list (or tail-call args), and the body
terminator, and checks they agree on the surviving vars.

A shared-site test asserts every edge lost the same positions and the entry
matches. An owned-cons test asserts a live head keeps its source projection and
a dead head removes both the capability and the physical entry param.

## Forbidden Shape

The capture set is fixed in the IR, not patched in codegen. Codegen reads the
continuation entry ABI as given; it does not look for unused closure fields to
skip storing. If a capture is dead, it is gone before codegen sees it.
