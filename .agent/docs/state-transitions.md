# State Transitions

Source calls, closure calls, continuation hops, recursive back edges, and
scheduler suspension have different runtime shapes, but the planner models them
all as state transitions over facts it already records: call-edge targets,
return-context plans, and callable capabilities. Passes read those facts rather
than reconstructing control shape from closure frames or capture order.

## Enum.reduce Shape

Runtime `Enum.reduce/3` delegates to `Enumerable.reduce_list/3`. `reduce_list`
is the public state dispatcher; the `:cont` path enters `reduce_list_cont/3`,
which carries the list and accumulator as first-class state instead of
re-threading a tagged reduce state through every hot step:

```text
state = (list, acc, reducer, outer_cont)

(list, {:halt, acc}, reducer, k) ->
  Return(k({:halted, acc}))

(list, {:suspend, acc}, reducer, k) ->
  Suspend(fn () -> reduce_list_cont(list, acc, reducer))

(list, {:cont, acc}, reducer, k) ->
  TailCall(reduce_list_cont, list, acc, reducer, k)

reduce_list_cont([], acc, reducer, k) ->
  Return(k({:done, acc}))

reduce_list_cont([h | t], acc, reducer, k) ->
  CallThen(reducer, h, acc,
    resume(result) = reduce_list_step(t, result, reducer, k))

reduce_list_step(t, {:cont, acc}, reducer, k) ->
  TailCall(reduce_list_cont, t, acc, reducer, k)
```

The hot loop state is `(list, acc, reducer)`. `reduce_list/3` is the public
state dispatcher; `reduce_list_step/3` handles reducer outputs that leave the
hot `:cont` path.

## Continuations Are Join Points First

A continuation body is a join point with captures. It becomes a heap closure
only when it escapes into a scheduler-visible or user-visible boundary.

Default model:

```text
join k(result, captures...) -> Step
```

Fallback representation:

```text
heap closure / lazy descriptor / scheduler root
```

Lazy-continuation materialization is therefore a representation choice, not a
semantic fact. The escape rule is precise: returning, storing, sending,
parking, or capturing a continuation into an escaping closure forces
materialization. A local join that immediately computes the next loop state
does not.

## Planner Vocabulary

The planner records each call edge as:

```text
CallEdgePlan {
  target,
  return_use,
  return_context,
}
```

These facts already carry continuation shape: how a callee result is consumed
lives in `return_context` (`ReturnContextPlan`), not in a separate dump-shape
recognizer. Loopification reads the same facts.

## Callable Values

`SpecPlan.callable_capabilities` carries callable identity as value-capability
data:

```text
CallableCapability =
  KnownFn(fn_id)
  KnownClosure { fn_id, captures }
  OpaqueCallable
```

The names describe what the compiler knows about a value, not which runtime
object must be built:

- `KnownFn` is a direct code identity with no runtime closure state. It can
  come from a zero-capture closure literal, but the useful fact is "this value
  can be called as this function," not "this value is a closure." The module
  inliner uses this: direct callsites to a `KnownFn` target can inline even when
  a zero-state closure value for the same function also exists elsewhere.
- `KnownClosure` is a direct code identity plus captured runtime state. It
  supports direct call edges, but the captures are real state and stay a
  representation barrier; the inliner keeps these targets callable as closure
  entries.
- `OpaqueCallable` is a callable boundary whose concrete target is not a single
  known function in this plan — for example, control flow that joins several
  zero-capture function values. It keeps the indirect-call shape and the
  conservative materialization rules; it stays closure-shaped and callable when
  it enters the `reduce_list_cont` state machine, and is not collapsed to one
  static identity.

Call-edge facts consume callable capabilities alongside `return_context`: the
target says what code may run, and the return context says how the result
becomes the next state. Provider-library planning runs this rewrite over the
linked working module, so a zero-state `Enum.reduce` reducer passed into
`reduce_list_cont/3` is an ordinary direct call by the time the module inliner
runs — spliced without a heap continuation or a stack lazy reducer descriptor.

## Proof Gates

- `Enum.reduce(xs, {:cont, 0}, reducer)` enters `reduce_list_cont/3` directly
  from the dispatcher.
- A local known reducer lowers `reduce_list` without the reducer-continuation
  trampoline.
- The known-reducer path keeps `closure_allocs = 0`.
- An opaque reducer join stays closure-shaped, callable, and
  heap-continuation-free inside the `reduce_list_cont` state machine
  (`fixtures/opaque_fn_value_join`).
- `{:suspend, acc}` is a real materialized resumable closure.
- `count_list`, `member_list?`, `foldl`, and `map(double, xs)` keep their
  allocation floors.
