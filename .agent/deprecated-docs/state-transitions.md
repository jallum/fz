# State Transitions

The runtime-library reduce family has two layers. `Enumerable.reduce/3` is the
protocol callback: it speaks Elixir's low-level tagged control state
(`{:cont, acc}` / `{:halt, acc}` / `{:suspend, acc}`) and answers in the matching
result tags (`{:done, acc}` / `{:halted, acc}` / `{:suspended, acc, cont}`).
Public `Enum.reduce/2,3` is the user-facing surface: its reducer returns a plain
accumulator, and `Enum` adapts that to and from the protocol tags.

Both layers share one engine. For a list, the work happens in three small
`List` functions that carry the list, accumulator, and reducer as ordinary
arguments rather than re-threading a tagged reduce state through every hot step.

The reducer is a callable value. The planner records its identity as a
[`CallableCapability`](dispatch-as-planner-output.md), and that one fact decides
whether the reducer call lowers to a direct call or an indirect one. That is the
key boundary in this subsystem: the *shape* of the reduce loop is fixed, but the
*reducer edge* inside it is direct or opaque depending on what the planner knows.

This is one application of the planner's general model: source calls, closure
calls, continuation hops, back edges, and suspension are state transitions over
recorded facts — call edges, return contracts, and callable capabilities — read
in codegen rather than reconstructed. See
[`dispatch-as-planner-output`](dispatch-as-planner-output.md) for those facts,
and [`lazy-continuation-materialization`](lazy-continuation-materialization.md)
for when a continuation in this machine becomes a heap closure.

## The List Reduce Engine

`Enumerable.reduce/3` dispatches on the receiver type to an implementation
callback. For a list that callback is `Enumerable.List.reduce/3` (the body of
`defimpl Enumerable, for: List`), which forwards straight to `List.reduce/3`.
`List.reduce/3` is the state dispatcher; the `:cont` clause enters
`List.reduce_cont/3`, which walks the cons cells; `List.reduce_step/3` dispatches
each reducer output and routes `:cont` back into the loop while peeling
`:halt`/`:suspend` out of the hot path.

```text
List.reduce(list, {:cont, acc}, reducer) ->
  List.reduce_cont(list, acc, reducer)

List.reduce(_list, {:halt, acc}, _reducer) ->
  {:halted, acc}

List.reduce(list, {:suspend, acc}, reducer) ->
  {:suspended, acc, (fn () -> List.reduce_cont(list, acc, reducer) end)}

List.reduce_cont([], acc, _reducer) ->
  {:done, acc}

List.reduce_cont([head | tail], acc, reducer) ->
  List.reduce_step(tail, reducer.(head, acc), reducer)

List.reduce_step(list, {:cont, acc}, reducer) ->
  List.reduce_cont(list, acc, reducer)
```

The hot loop state is `(list, acc, reducer)`. `List.reduce_cont/3` is the
recursive tail-call loop over the list; `List.reduce_step/3` keeps the tagged
reducer-output dispatch off that loop's fast edge. A `{:suspend, acc}` result is
the one place the loop hands back a real value: a `{:suspended, acc, cont}` tuple
whose third element is a materialized resumable closure, not an internal
continuation edge.

## Public Enum.reduce

`Enum.reduce/3` is not the protocol callback. It is a thin wrapper that lets user
code write a reducer returning the next accumulator directly. `Enum.reduce/3`
wraps each user result as `{:cont, acc}` for the protocol machine, then peels the
final `{:done, acc}` / `{:halted, acc}` / `{:suspended, acc, _}` with
`reduce_finish/1`:

```text
Enum.reduce(enumerable, acc, reducer) ->
  reduce_finish(
    Enumerable.reduce(enumerable, {:cont, acc}, fn entry, inner_acc ->
      {:cont, reducer.(entry, inner_acc)}
    end))
```

`Enum.reduce/2` is the same idea with a first-element seed: it threads a
`:first` / `{:acc, value}` state through `reduce_first_step/3` and unwraps it with
`reduce_first_finish/1`, raising `Enum.EmptyError` on an empty input.

Public `Enum` carries no separate list shortcut. The route to the list engine is
the protocol dispatch fact: for a known list receiver, static protocol dispatch
sends `Enumerable.reduce/3` to `Enumerable.List.reduce/3`, which delegates to
`List.reduce/3` and so reaches `List.reduce_cont/3`. The public wrapper bridge
allocates one closure (the `fn entry, inner_acc -> {:cont, ...}` adapter).

Most of `Enum`'s higher-order list functions are not built on the reduce engine
at all. `map/2`, `filter/2`, `reject/2`, `flat_map/2`, `map_reduce/3`,
`scan/2,3`, `intersperse/2`, `with_index/1,2`, `map_every/3`, `map_join/2,3`, and
`map_intersperse/3` normalize the input through `to_list/1` and then call a
module-local private builder (`map_list`, `filter_list`, …) written as ordinary
recursive list construction, so native return-demand lowering can deliver the
built list in place. `with_index/2` carries both Elixir shapes — an integer
offset and an `(entry, index) -> value` mapper — and `Enum` has no public
`with_index/3`. The two `with_index/2` shapes are written as two `@spec` arrows
so a same-name/same-arity overload keeps each arrow's input-to-result
correlation instead of collapsing the positions into one union (see
[`specs`](specs.md)).

## Known vs Opaque Reducers

The reducer's `CallableCapability` decides how the `reducer.(head, acc)` call
inside the loop lowers:

- A `KnownFn` reducer is a single code identity. Its call edge becomes a direct
  call, so the loop runs with no reducer-continuation trampoline and allocates no
  closure for the reducer.
- An `OpaqueCallable` reducer is a callable boundary whose concrete target is not
  one known function — for example a control-flow join of two different
  zero-capture function values, which cannot be treated as one static reducer
  identity. Its call stays an indirect call. Inside `List.reduce_cont/3` that
  reducer continuation is kept as a lazy descriptor: closure-shaped and callable,
  but not forced into a heap closure.

(`CallableCapability` also has a `KnownClosure { fn_id, captures, .. }` variant
for a known function paired with captured environment; the reduce engine threads
a captured reducer through the same loop.)

Provider-library planning runs this rewrite over the linked working module, so a
protocol callsite with a known receiver is resolved to the protocol-owned
implementation body before native emission. The `{:suspend, acc}` result is the
exception to "internal continuation, not a value": it is a real, materialized
resumable closure handed back to the caller as a source-visible value.

## A Tiny Walkthrough

```text
Enum.reduce([1, 2, 3], 0, fn x, acc -> acc + x end)
  Enum.reduce wraps:  reducer'(x, acc) = {:cont, acc + x}   (one closure alloc)
  Enumerable.reduce([1,2,3], {:cont, 0}, reducer')
    static dispatch -> Enumerable.List.reduce -> List.reduce
    List.reduce(.., {:cont, 0}, ..) -> List.reduce_cont([1,2,3], 0, ..)
      reducer' is KnownFn -> direct call, no trampoline
      cons walk: 0 -> 1 -> 3 -> 6, tail-call loop, no extra cons cells
    [] -> {:done, 6}
  reduce_finish({:done, 6}) -> 6
```

## Ownership And Contracts

- `Enumerable.reduce/3` is the protocol seam that hands back the result tags
  `{:done|:halted|:suspended, ...}`. The input tags `{:cont|:halt|:suspend, acc}`
  are spoken across the protocol surface: `Enum.reduce/2,3` wrap a plain
  accumulator into `{:cont, acc}`, and `Enum.reduce_while/3` passes a user reducer
  that returns `{:cont, acc}` / `{:halt, acc}` straight through. `List.reduce/3`
  and `List.reduce_step/3` consume those input tags and emit the result tags.
- `List.reduce_cont/3` owns the cons walk and stays a recursive tail call
  (lowers to `return_call`); `List.reduce_step/3` owns reducer-output dispatch.
- `Enum.reduce/2,3` owns the value↔tag adaptation (the `{:cont, ...}` wrapper and
  `reduce_finish`), and owns the single bridge-closure allocation.
- The planner owns the reducer identity via `CallableCapability`: `KnownFn` makes
  the reducer call direct and trampoline-free; `OpaqueCallable` keeps it indirect
  with a lazy-descriptor continuation; neither forces a heap continuation in the
  list reducer path.

Telemetry-observable contracts that fix the boundaries: the
`Enumerable.List.reduce` body lowers without `call_indirect` for a known list
receiver and `List.reduce_cont` keeps `return_call` (`enum_list_allocations`); an
opaque reducer join emits a `["fz","codegen","closure_call_lowered"]` event with
`dispatch_kind = indirect` and `continuation_storage = lazy_descriptor` and
lowers through `List.reduce_cont` without `@fz_alloc_closure`
(`opaque_fn_value_join`). The public Elixir-style values of the reduce surface
and the map family are pinned by `enum_tier0` and `enum_map_family`. All four
run across the interpreter, JIT, AOT, and REPL paths.
