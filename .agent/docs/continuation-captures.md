# Continuation Captures

## Model

Continuation captures are dataflow, not scope. Scope answers what names the
lowerer can look up; capture shape answers what values the continuation
actually needs later. A variable should not enter a continuation just because
it was visible when the continuation was created.

The lowered IR may create conservative capture candidates. The canonical
boundary is `ir_capture_norm`. After that pass:

```text
continuation captures = unique caller Vars actually read by the continuation
```

No unused capture. No duplicate capture of the same caller `Var`.

Capture shape is independent of materialization. A compiler-known native
continuation can carry these same captures in a stack-backed lazy descriptor
until a scheduler boundary requires an ordinary heap closure. See
[`lazy-continuation-materialization.md`](lazy-continuation-materialization.md).

## What The Pass Owns

`ir_capture_norm` normalizes:

- `Term::Call` continuations
- `Term::CallClosure` continuations
- tail-call continuation args
- `Term::ReceiveMatched` shared captures

It runs during lowering after brand erasure and before planner/codegen consumers
depend on continuation ABI shape.

Shared continuation sites are normalized as a unit. If several branches feed
the same continuation body, `ir_capture_norm` computes which captured positions
survive local DCE and removes the same dead positions from every edge. That
keeps the continuation entry params, every call edge, and every closure or lazy
descriptor payload in one shape.

Owned-cons reuse capabilities are physical facts, not ordinary user values.
Local DCE may remove the source cons variable because no source expression reads
it again, but codegen still needs that source cons if the live head capture
carries an owned-reuse capability. `ir_dce` therefore treats `source_cons` as
physically live when the capability's `head` is semantically live, and drops the
capability and its physical entry param when the head is not semantically used.
`ir_capture_norm` rewrites capture shapes and then runs ordinary DCE; it does
not carry a separate owned-cons repair path.

## Lambda Captures

Lambda closures use the same idea earlier: capture the lambda body's free
outer names, not every visible local.

```text
fn outer(x, y), do: fn(z) -> x + z
```

The lambda captures `x`. It does not capture `y`.

## Tests

Use telemetry to prove the pass made the decision:

```text
fz.ir.capture_norm.captures_pruned
before_captures: 2
after_captures: 1
pruned_captures: 1
```

Use structural assertions to prove the IR is right:

```text
cont k captured=[only_live_var]
entry params match captured vars
call edge args match entry params
```

For shared continuation sites, assert every edge lost the same dead positions.
For owned-cons reuse, assert live head capabilities still carry their source cons
and dead head capabilities disappear before codegen.

Telemetry proves the compiler acted. Structure proves it acted correctly.

## Forbidden Shape

Do not fix capture bloat in codegen.

Bad:

```text
codegen sees unused closure field and skips the store
```

Good:

```text
IR never carries the unused capture into codegen
```

Keep codegen boring. Make the IR correct first.
