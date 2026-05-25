# Continuation Captures

Continuation captures are dataflow, not scope.

## ELI5

Scope answers:

```text
What names can the lowerer look up here?
```

Capture shape answers:

```text
What values does this continuation actually need later?
```

Those are not the same question. A variable should not enter a continuation
just because it was visible when the continuation was created.

## Rule

The lowered IR may create conservative capture candidates. The canonical
boundary is `ir_capture_norm`.

After that pass:

```text
continuation captures = unique caller Vars actually read by the continuation
```

No unused capture. No duplicate capture of the same caller `Var`.

## What The Pass Owns

`ir_capture_norm` normalizes:

- `Term::Call` continuations
- `Term::CallClosure` continuations
- `Term::Receive` continuations
- tail-call continuation args
- `Term::ReceiveMatched` shared captures

It runs during lowering after brand erasure and before typer/codegen consumers
depend on continuation ABI shape.

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
