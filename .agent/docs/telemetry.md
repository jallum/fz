# Telemetry

Telemetry is the compiler writing down what it already knows while it works.
Use it when a question starts with "why did the compiler do that?" or "where is
the time going?"

## The Idea

Do not guess. Make the compiler leave breadcrumbs.

Good telemetry is:

- cheap when nobody is listening
- made from facts already in hand
- structural enough for tests to inspect
- boring to emit from compiler code
- useful before, during, and after a performance fix

Think of each event as: "at this point in the pipeline, here are the facts that
explain what just happened."

## What To Put In Events

Put in values that are natural byproducts of the current work:

- module name
- function name
- block id
- spec key
- counts already computed
- elapsed time for a span
- reason something was consumed, skipped, stalled, or pruned

If a value is expensive to compute, do not compute it just for telemetry. Prefer
passing borrowed structure as metadata and let a live handler inspect it if it
cares.

JSON logs can skip opaque structural values. Live handlers can use them during
the event.

## The Workflow

1. Add a small event or span where the compiler already has the fact.
2. Run a real fixture, not a toy if the bug is not toy-sized.
3. Compare the telemetry to the source program.
4. Name the weird thing.
5. Fix the data model or algorithm.
6. Pin the improvement with tests or fixture budgets.

Example:

```text
question: why is quicksort slow to compile?
telemetry: typer dominates, with many worklist/type_fn calls
finding: we were retyping from caution
fix: reuse frontend types and skip impossible specs
result: quicksort worklist pops 232 -> 142, type_fn calls 78 -> 47
```

## What It Found For Us

Telemetry showed that the typer was doing repeated work and producing more
specialization shapes than the source program justified.

Across fixture budgets:

```text
typer worklist pops: 1032 -> 888
typer walk calls:    1032 -> 888
typer type_fn calls:  477 -> 416
typer dispatches:     327 -> 217
```

That churn is good churn: the compiler got simpler.