# Runtime Transport Story

This is the one story compiler2 should be telling from semantics down to native codegen.

## Core Rule

A callable value is a runtime transport object with a settled payload shape.

Once semantics and artifact have decided that shape, downstream code does not get to reinterpret it, widen it, narrow it, or recover it from some smaller summary. Native lowering and codegen only execute the plan.

## Two Facts, Not One

Compiler2 must keep two facts separate.

1. Semantic/runtime transport fact
   This answers: what exact runtime value shape must exist and move through the program?

2. Boundary ABI fact
   This answers: if control crosses a callable boundary, what entry/return contract must that boundary expose?

These are related, but they are not interchangeable.

`ReturnAbi` is a boundary fact. It is not the internal truth for executable returns, delivered resumes, continuation payloads, or closure payloads.

## Semantic Story

When the program forms a first-class callable or continuation, semantics already knows:

- which executable body will run
- which values are captured
- which captured values matter at runtime
- the runtime shape of each carried value

By the time we leave semantic analysis, there should be no unresolved question like:

- should this lane be `RawInt` or `ValueRef`?
- should this callable be widened and then narrowed later?
- should this return be flattened now and reconstructed later?

Those are already decided.

## Artifact Story

Artifact freezes runtime transport as one structural model:

- `Omitted`
- `Value { ty, repr }`
- `TupleFields { fields }`
- `DirectCallable { function, captures }`

This same model must describe all internal transport seams:

- executable returns
- delivered resumes
- continuation captures
- closure captures
- direct-callable values

Artifact may also derive boundary contracts where needed, but those are secondary products. The structural runtime layout is the authoritative internal fact.

## Native Lowering Story

Native lowering should not rediscover layout from:

- `ReturnAbi`
- `param_reprs`
- local capture lists
- continuation conventions
- closure-target conventions

Native lowering should do only two things:

1. carry the settled runtime layout facts onto native bodies and helper records
2. map source values into those layouts mechanically

Examples:

- if a continuation capture layout says slot 0 is `RawInt`, store raw int
- if slot 1 is `ValueRef`, store ref
- if a delivered resume layout is tuple fields, flatten exactly those fields
- if a value is a `DirectCallable`, preserve that structure instead of collapsing it to `ValueRef`

No local reinterpretation belongs here.

## Codegen Story

Codegen should be boring.

For every transport seam, codegen should:

1. write payload lanes according to the settled runtime layout
2. read payload lanes according to the same settled runtime layout
3. replay yielded or resumed values according to the same settled runtime layout

This means heap closures, continuation closures, yielded continuations, resumed continuations, and direct callable materialization are not distinct modeling problems. They are the same operation:

serialize a runtime value into a transport object according to a settled layout, then deserialize it later using that same layout

If codegen has separate local decision engines for these cases, those are signs that authority has leaked downward.

## ABI Story

ABI facts are only for real boundaries.

Use boundary contracts for:

- crossing a callable boundary
- exposing a first-class callable entry surface
- adapting values at a true boundary

Do not use boundary contracts as the internal model for:

- executable return structure
- continuation payload structure
- closure capture structure
- yielded continuation payloads

Internal transport should always flow from the structural runtime layout fact.

## What Must Be Removed

The following ideas are wrong wherever they appear:

- captures are fundamentally ref words and can always be narrowed later
- executable returns can be represented internally by `ReturnAbi`
- yielded continuations need their own transport model
- entry param reprs are a substitute for capture layout
- local codegen conventions may override settled runtime layout facts

These produce duplicated authority and force downstream layers to recover information that was already known earlier.

## Correctness Standard

At every seam, ask one question:

What exact runtime layout fact did artifact settle for this value?

Then:

- write that layout
- read that layout
- nothing else

If any layer has to guess, widen, recover, or reinterpret, the model is wrong in that layer.
