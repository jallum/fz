# State Transitions

## Goal

Model control before representation. Source calls, closure calls,
continuation hops, recursive back edges, and scheduler suspension have
different runtime shapes, but planner/codegen should consume the existing
call-edge and return-context facts before reconstructing anything from closure
frames or capture order.

## Enum.reduce Shape

Runtime `Enum.reduce/3` delegates to `Enumerable.reduce_list/3`.
`reduce_list` is the public state dispatcher; the `:cont` path enters
`reduce_list_cont/3`, which carries the list and accumulator as first-class
state instead of re-threading a tagged reduce state through every hot step:

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

This is the useful source-level simplification: the hot loop state is
`(list, acc, reducer)`. `reduce_list/3` remains the public state dispatcher;
`reduce_list_step/3` handles reducer outputs that leave the hot `:cont` path.

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

This keeps lazy-continuation materialization as a representation choice, not a
semantic fact. It also keeps the escape rule precise: returning, storing,
sending, parking, or capturing a continuation into an escaping closure forces
materialization. A local join that immediately computes the next loop state
does not.

## Planner Vocabulary

Do not add another recognizer just to rediscover continuation shape. The
planner already records:

```text
CallEdgePlan {
  target,
  return_use,
  return_context,
}
```

Loopification should make new behavior fall out of these facts. If a pass needs
to know how a callee result is consumed, extend `ReturnContextPlan`; do not add
a parallel `resume=` dump recognizer.

## Callable Values

`SpecPlan.fn_constants` currently carries a side-channel for zero-capture
function identity. That is useful, but narrower than the transition model. The
longer-term shape should make callable identity part of value capability data:

```text
Callable =
  KnownFn(fn_id)
  KnownClosure(fn_id, captures)
  OpaqueCallable(arity, effects, return)
  Union(KnownFn..., KnownClosure..., OpaqueCallable...)
```

These names describe what the compiler knows, not which runtime object must be
built:

- `KnownFn` is a direct code identity with no runtime closure state. It may come
  from a zero-capture closure literal, but consumers must treat the useful fact
  as "this value can be called as this function" rather than "this value must be
  represented as a closure." The module inliner consumes this distinction:
  direct callsites to `KnownFn` targets may inline even if a zero-state closure
  value also exists elsewhere in the module.
- `KnownClosure` is a direct code identity plus captured runtime state. It can
  still support direct call edges, but the captures are real state and remain a
  representation barrier until a pass proves otherwise. Inlining must keep these
  targets callable as closure entries.
- `OpaqueCallable` is a callable boundary whose concrete target is not a single
  known function in the current plan. It keeps the indirect-call shape and the
  conservative materialization rules.

Planner call-edge facts can then consume callable capabilities uniformly with
`ReturnContextPlan`: the target tells us what code may run, and the return
context tells us how the result becomes the next state. The remaining
known-reducer timing work is tracked by `fz-xac`: expose closure-literal reducer
calls early enough for module-level inlining without forcing heap continuation
materialization.

## Proof Gates

When changing this area, keep these signals explicit:

- `Enum.reduce(xs, {:cont, 0}, reducer)` enters `reduce_list_cont/3` directly
  from the dispatcher.
- Local known-reducer `reduce_list` lowers without the reducer-continuation
  trampoline.
- Known reducer path keeps `closure_allocs = 0`.
- Opaque reducer path still loopifies around an indirect call.
- `{:suspend, acc}` remains a real materialized resumable closure.
- `count_list`, `member_list?`, `foldl`, and `map(double, xs)` do not regress.

## Removal Targets

This model should let future work remove or demote:

- closure-shaped local continuations as the default representation;
- special passes whose only job is to erase function values after direct-call
  planning has already made them dead;
- duplicated callsite-shape logic that can instead read planner call-edge and
  return-context facts.
