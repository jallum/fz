# Continuation Capture Normalization Research

Ticket: `fz-0k7.18.1`

## ELI5

The lowerer currently builds a continuation by taking a photo of every name in
scope. That photo becomes the continuation's function parameters and, later, the
heap closure captures that codegen stores.

That is the wrong owner for the decision. Scope answers "what names can I look
up while lowering this source expression?" Capture shape answers "what data does
this continuation body actually read after the call returns?" Those are related,
but they are not the same thing.

The correct rule is:

```text
Continuation captures = unique free variables actually used by the continuation body.
```

No variable should be captured because it merely happened to be in lexical
scope. No same `Var` should be captured twice through two env names.

## Current Producers

### Non-tail direct calls

`src/ir_lower.rs::cps_split_call` snapshots every env binding:

```text
captured = ctx.captured_snapshot()
Term::Call { continuation: Cont { captured } }
new k entry params = [result, ...captured]
```

This is the quicksort `qsort(hi) -> k_33` producer.

### Non-tail closure calls

`src/ir_lower.rs::cps_split_call_closure` uses the same shape as direct calls:

```text
Term::CallClosure { continuation: Cont { captured } }
new k entry params = [result, ...captured]
```

The normalizer should treat this identically to `Term::Call`.

### Receive

`src/ir_lower.rs::cps_split_receive` also snapshots every env binding and builds
a continuation entry `[message, ...captured]`.

Receive continuations must keep values needed after park/resume. Values merely
in scope should disappear. This does not change the scheduler model: the
scheduler still sees a runnable closure/root, just with fewer captures.

### Branch, case, cond, with, and clause continuations

`mint_cont_fn` stores `outer_captured = ctx.captured_snapshot()`, and
`switch_to_cont_fn` builds entry params from that snapshot. Users include:

- `lower_if`
- `lower_case`
- `lower_cond`
- `lower_with`
- `lower_multi_clause`
- pattern-matrix clause continuations

These continuations are often later inlined, but not always. The same dataflow
rule should apply: when a continuation survives as a function, its extra params
should be exactly the free values the body reads.

### Lambda closure capture

`lower_lambda` captures every in-scope local before building the lambda body.
Existing ticket `fz-9rs` already names this narrower problem:

```text
lambda lifter: capture only free variables actually referenced in the body
```

The lambda fix should use the same free-var engine where practical, but it is
slightly different mechanically because `Prim::MakeClosure(_, fn_id, captured)`
is the producer instead of `Cont { captured }`.

## Current Consumers

### DCE

`src/ir_dce.rs::collect_term_vars` treats `continuation.captured` as real uses.
That is correct once captures are canonical, but it means DCE cannot remove
overcaptures after lowering has made them part of the call edge.

### Inline passes

`src/ir_inline.rs::inline_calls_once` rewrites an inlined callee return to:

```text
TailCall(K, [result, ...cont_captured])
```

`inline_single_use_conts_once` only absorbs continuation sites whose
`Cont.captured` is empty. Non-empty overcaptured continuations therefore survive.

### Typer

`src/ir_typer.rs::cont_key_for_spec` and `cont_input_key` build continuation
keys from the returned value plus `continuation.captured`. Overcaptures become
type-specialization surface area and can multiply work.

### Interpreter

`src/ir_interp.rs` collects `continuation.captured` into continuation/runtime
state for `Term::Call`, `Term::CallClosure`, and `Term::Receive`.

### Codegen

`src/ir_codegen.rs::emit_terminator` builds continuation closures from
`continuation.captured`, and `build_cont_closure` stores those captures through
the closure ABI. Codegen is mostly faithful here; it should receive honest IR
instead of hiding bad capture lists with a peephole.

## Quicksort Walkthrough

Source:

```fz
fn qsort([p | rest]) do
  {lo, hi} = partition(p, rest, [], [])
  append(qsort(lo), [p | qsort(hi)])
end
```

Current typed bodies show:

```text
k_31:
  Call qsort(lo)
  cont k_32 captured=[p, rest, lo, hi]

k_32:
  Call qsort(hi)
  cont k_33 captured=[p, rest, lo, hi, sorted_lo, p]

k_33:
  tail = [p | sorted_hi]
  append(sorted_lo, tail)
```

`k_33` needs:

```text
p
sorted_lo
outer_cont (runtime closure field 0)
```

It does not need:

```text
rest
lo
hi
```

The duplicate `p` comes from `park()`. List lowering parks element results under
synthetic `_tN` names before lowering the tail. For `[p | qsort(hi)]`, both the
source name `p` and a temporary name point to the same `Var`, and
`captured_snapshot()` captures names instead of unique dataflow vars.

## Desired Pass

Add a canonical IR pass:

```text
normalize_continuation_captures_with_telemetry(module, tel)
```

Run it after lower/brand erasure/back-edge annotation and before typer/codegen
consumers rely on continuation keys. Emit a pruning telemetry event whenever
the pass changes a continuation shape, so tests can prove the pass fired without
depending only on incidental IR shape.

For each unique continuation `K` referenced by `Term::Call`,
`Term::CallClosure`, or `Term::Receive`:

1. Find the single continuation site. The lowerer's unique-cont invariant should
   already guarantee this.
2. Inspect `K`'s entry block. Slot 0 is the result/message param. Slots 1..N are
   captured params corresponding positionally to `Cont.captured`.
3. Compute which captured entry params are used anywhere in `K`.
4. Deduplicate `Cont.captured` by `Var`. If two capture positions pass the same
   caller `Var`, rewrite all uses of the later entry param to the earlier entry
   param.
5. Drop unused captured entry params and their matching `Cont.captured` entries.
6. Preserve result/message param and block source metadata.
7. Rebuild fn indexes if needed, though the pass should not remove functions.

The pass should not touch:

- normal user function params
- tail-call args that are not `Cont.captured`
- closure target captures from `Prim::MakeClosure` until the lambda ticket

## Thorn Strategies

### Entry param use includes terminators

Use the same style as DCE: collect vars used in stmts and terminators. For this
pass, the question is specific to a continuation fn's entry captured params, not
all vars.

### Rewriting duplicate params

When duplicate caller vars exist:

```text
Cont.captured = [p, p]
K params      = [result, cap0, cap1]
```

rewrite all uses of `cap1` in `K` to `cap0`, then drop `cap1` and the second
captured operand.

### Multiple blocks

Continuation bodies can have multiple blocks. The rewrite must walk every block
stmt and terminator in that fn.

### Receive

`Receive` has no callee args but the continuation shape is the same:

```text
K params = [message, ...captured]
```

The message param must always remain. Captures still normalize.

### Branch and clause continuations

These may be reached by `TailCall`, not `Cont`. A second phase should normalize
single-entry continuation functions whose category identifies them as
control-flow/multi-clause continuations and whose incoming tail-call sites use
the same positional capture shape.

Do this only after the call/receive `Cont` path is proven, because the call path
is simpler and directly fixes quicksort.

### Lambda capture

Lambda capture should be handled with the same free-var idea but a separate
rewrite:

```text
Prim::MakeClosure(fid, captured)
lambda entry params = [captured..., user params...]
```

Compute used captured entry params in the lambda body, rewrite duplicates, drop
unused captured params, and update every `MakeClosure` site for that lambda
shape. This intersects existing `fz-9rs`.

## Acceptance Shape

For quicksort, after the call/receive continuation pass:

```text
k_32:
  cont k_33 captured=[sorted_lo, p]

k_33:
  params=[sorted_hi, sorted_lo, p]
```

Codegen will then naturally allocate a smaller continuation closure:

```text
closure fields:
  0 outer_cont
  1 sorted_lo
  2 p
```

No codegen-specific quicksort peephole is required.
