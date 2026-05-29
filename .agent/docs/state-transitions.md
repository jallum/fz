# State Transitions

## Goal

Model control before representation. A source call, closure call,
continuation hop, recursive back edge, and scheduler suspension are different
runtime shapes, but the planner should first describe them as transitions
between explicit machine states.

The target vocabulary is:

```text
Step =
  Return(value)
  Jump(target, args...)
  CallThen(target, args..., resume)
  Suspend(resume_state)
  Halt(reason)
```

`CallThen` is the load-bearing case. It is one logical edge made from a callee
and the continuation that receives the callee's result. Existing IR stores that
as `Term::Call` / `Term::CallClosure` plus `Cont`; planner facts should be the
source of truth for the combined transition. Codegen must not rediscover it
from closure frames or capture order.

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

The current CLIF shape still makes the hot path look like a trampoline:

```text
reduce_list -> reducer -> k_result -> reduce_list
```

The intended normalized shape is a loop over the state tuple, with the reducer
call inside the loop. Static closure identity is only an optional improvement:
a known reducer can be called directly or inlined, while an opaque reducer can
still sit inside the same loop as an indirect call.

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

## Loopification Rule

A conservative first loopification target is:

```text
F(state...) CallThen G(args..., resume = K(captures...))
K(result, captures...) TailCall F(next_state(result, captures...))
```

When `F` is in the same recursive family and `K` only builds the next state, the
combined edge is a loop update. The rule is independent of whether `G` is a
direct function, known closure, closure literal, or opaque closure call.

The first implementation should support self-recursive single-cycle cases. The
model leaves room for mutual-recursive SCC loops later.

## Callable Values

`SpecPlan.fn_constants` currently carries a side-channel for zero-capture
function identity. That is useful, but narrower than the transition model. The
longer-term shape should make callable identity part of value capability data:

```text
Callable =
  KnownFn(fn_id, captures)
  OpaqueArrow(arity, effects, return)
  Union(KnownFn..., OpaqueArrow...)
```

Planner call-edge facts can then consume callable capabilities uniformly.
Known closure erasure becomes a consequence of state/call planning instead of a
separate cleanup whose job is to undo closure-shaped plumbing.

## Proof Gates

When changing this area, keep these signals explicit:

- `Enum.reduce(xs, {:cont, 0}, reducer)` hot path is recognized as
  `CallThen(reducer, ..., resume = reduce_list(...))`.
- Known reducer path keeps `closure_allocs = 0`.
- Opaque reducer path still loopifies around an indirect call.
- `{:suspend, acc}` remains a real materialized resumable closure.
- `count_list`, `member_list?`, `foldl`, and `map(double, xs)` do not regress.

## Removal Targets

This model should let future work remove or demote:

- backend-local reconstruction of continuation state from capture order;
- closure-shaped local continuations as the default representation;
- special passes whose only job is to erase function values after direct-call
  planning has already made them dead;
- duplicated callsite-shape logic that can instead read planner `CallThen`
  facts.
