# State Transitions

The runtime-library `reduce` family lowers a recursive higher-order loop into an
explicit state machine. The hot loop is carried as ordinary first-class values —
the list, the accumulator, and the reducer — by `reduce_list_cont/3`. The tagged
reduce state (`{:cont, acc}` / `{:halt, acc}` / `{:suspend, acc}`) is peeled by
the dispatchers (`reduce_list/3` at entry, `reduce_list_step/3` on each reducer
result) rather than re-threaded through the hot carrier itself.

This is one application of the planner's general model: source calls, closure
calls, continuation hops, back edges, and suspension are all state transitions
over recorded facts — call edges, return contexts, and callable capabilities —
read rather than reconstructed in codegen. See
[`dispatch-as-planner-output`](dispatch-as-planner-output.md) for those
facts, and [`lazy-continuation-materialization`](lazy-continuation-materialization.md)
for when a continuation in this machine becomes a heap closure.

## Enum.reduce Shape

Runtime `Enum.reduce/3` delegates to `Enumerable.reduce_list/3`. `reduce_list`
is the public state dispatcher; the `:cont` path enters `reduce_list_cont/3`,
which carries the list and accumulator as first-class state instead of
re-threading a tagged reduce state through every hot step:

```text
state = (list, acc, reducer)

reduce_list(list, {:cont, acc}, reducer) ->
  reduce_list_cont(list, acc, reducer)

reduce_list(_list, {:halt, acc}, _reducer) ->
  {:halted, acc}

reduce_list(list, {:suspend, acc}, reducer) ->
  {:suspended, acc, (fn () -> reduce_list_cont(list, acc, reducer))}

reduce_list_cont([], acc, _reducer) ->
  {:done, acc}

reduce_list_cont([h | t], acc, reducer) ->
  reduce_list_step(t, reducer(h, acc), reducer)

reduce_list_step(list, {:cont, acc}, reducer) ->
  reduce_list_cont(list, acc, reducer)
```

The hot loop state is `(list, acc, reducer)`. `reduce_list/3` is the public
state dispatcher; `reduce_list_step/3` dispatches each reducer output, routing
`:cont` back into `reduce_list_cont/3` and peeling `:halt`/`:suspend` out of the
hot path.

## Known vs Opaque Reducers

The reducer threaded through the machine is a callable value, and the planner
records its identity as a
[`CallableCapability`](dispatch-as-planner-output.md):

- A `KnownFn` reducer is a direct code identity. Its call edges become direct
  calls, so the known-reducer path runs without a reducer-continuation
  trampoline and allocates no closure.
- An `OpaqueCallable` reducer is a callable boundary whose concrete target is not
  one known function — for example a join of several zero-capture function
  values. It keeps the indirect-call shape and stays closure-shaped and
  heap-continuation-free inside the `reduce_list_cont` state machine.

Provider-library planning runs this rewrite over the linked working module, so a
zero-state `Enum.reduce` reducer passed into `reduce_list_cont/3` is an ordinary
direct call by the time the module inliner runs — spliced without a heap
continuation or a stack lazy reducer descriptor. A `{:suspend, acc}` result is
different: it is a real, materialized resumable closure, a source-visible value
rather than an internal continuation edge.

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
- `count_list` and `member_list?` keep their allocation floors alongside
  `Enum.reduce/3` (`fixtures/enum_list_allocations`: `list_cons_allocs = 5`,
  `closure_allocs = 0`).
- `foldl` and `map(double, xs)` (`fixtures/list_primitives`) keep their spec
  baseline (16 specs, 0 matchers) exercising cons-pattern dispatch and
  first-class fns passed in.
