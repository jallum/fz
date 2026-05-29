# Telemetry

## Model

Telemetry is the compiler writing down facts it already knows while it works.
Use it when a question starts with "why did this happen?", "how many did we
change?", or "which path did the compiler take?"

Do not guess. Make the compiler leave breadcrumbs.

This doc covers compile-time telemetry. For the running scheduler's events —
process exit, dbg output, and how tests observe a run — see
[`runtime-telemetry`](runtime-telemetry.md).

Good telemetry is:

- cheap when nobody is listening
- made from facts already in hand
- precise enough for tests to inspect
- boring to emit from compiler code
- useful during research, performance work, implementation, and regression tests

Think of each event as:

```text
At this point in the pipeline, this thing happened for this reason.
```

## Telemetry For Performance

Performance work starts with finding the expensive shape, not guessing at the
fix.

Use telemetry to answer:

- where did the compiler spend work?
- how many times did this pass visit the same thing?
- how many shapes, blocks, functions, dispatches, boxes, or helper calls were
  produced?
- which source construct caused the churn?
- did the fix reduce the count we meant to reduce?

The workflow is:

1. Add a cheap event, span, or counter where the compiler already has the fact.
2. Run a real fixture that shows the problem.
3. Compare the telemetry to the source program.
4. Name the waste.
5. Fix the data model or algorithm.
6. Keep the useful counter as a budget, regression test, or diagnostic event.

Example:

```text
question: why is this fixture generating too much code?
telemetry: one source operation produces five helper calls and three boxes
finding: the IR is carrying the same value in split forms
fix: make the IR carry the value once
result: helper calls and boxes drop, and the output shape is smaller
```

Good performance telemetry measures the thing you want to make smaller. If the
goal is fewer generated instructions, count the operations that cause them. If
the goal is less repeated type work, count visits, cache hits, and dispatches.

## Telemetry In Tests

Telemetry is a good test oracle for process facts:

- a pass ran
- a path was selected
- an optimization fired
- a value was pruned, skipped, folded, consumed, boxed, copied, or rejected
- a count changed from N to M
- a reason was recorded

Telemetry is not a replacement for checking the produced artifact.

Use structural assertions for product facts:

- the IR has the right shape
- the ABI has the right parameters
- the CLIF contains or omits the expected operation
- a rewritten value points at the right variable
- a fixture still runs and prints the right result

The strong pattern is both:

```text
telemetry proves: the compiler made the intended decision
structure proves: the decision produced the right program
```

## Testing Shape

A telemetry-backed test should usually:

1. Attach a capture handler.
2. Run the smallest pipeline that owns the behavior.
3. Assert the event name.
4. Assert the producer or reason.
5. Assert the important measurements.
6. Assert the final artifact shape when shape matters.

Example:

```text
event:      fz.ir.some_pass.items_pruned
producer:   call_continuation
before:     3
after:      1
pruned:     2
```

That proves the pass intentionally pruned two items. A separate structural
assertion should still prove the rewritten continuation has the one correct
item.

## What To Put In Events

Put in values that are natural byproducts of the current work:

- module name
- function name
- block id
- pass or producer name
- before and after counts
- reason something was consumed, skipped, stalled, pruned, or rejected
- elapsed time for a span, when timing is the question

Do not compute expensive data just for telemetry. If nobody is listening,
telemetry should be nearly free.

Prefer small, stable fields that tests can match. Avoid dumping huge debug
strings and then parsing them in tests.

## Naming

Event names should read from broad to specific:

```text
fz.<area>.<pass>.<thing_that_happened>
```

Examples:

```text
fz.ir.capture_norm.captures_pruned
fz.ir.dce.block_pruned
fz.codegen.function_lowered
```

Use metadata for identity and reasons. Use measurements for numbers.

## When To Reach For Which

If the test is asking "did the compiler do the work I expected?", use
telemetry.

If the test is asking "is the resulting program representation correct?",
inspect the representation.

If both questions matter, test both.
