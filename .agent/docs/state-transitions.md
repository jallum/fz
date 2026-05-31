# State Transitions

The runtime-library reduce family has two layers. `Enumerable.reduce/3` is the
protocol callback and uses Elixir's low-level tagged control state
(`{:cont, acc}` / `{:halt, acc}` / `{:suspend, acc}`). Public `Enum.reduce/2,3`
returns accumulator values and keeps known-list traversal in a tight local loop
that carries only the list, accumulator, and reducer.

This is one application of the planner's general model: source calls, closure
calls, continuation hops, back edges, and suspension are all state transitions
over recorded facts — call edges, return contexts, and callable capabilities —
read rather than reconstructed in codegen. See
[`dispatch-as-planner-output`](dispatch-as-planner-output.md) for those
facts, and [`lazy-continuation-materialization`](lazy-continuation-materialization.md)
for when a continuation in this machine becomes a heap closure.

## Enumerable.reduce Shape

Runtime `Enumerable.reduce/3` dispatches to implementation callbacks such as
`Enumerable.List.reduce/3`. The list implementation's `reduce_list/3` is the
protocol state dispatcher; the `:cont` path enters `reduce_list_cont/3`,
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
  reduce_list_step(t, reducer.(h, acc), reducer)

reduce_list_step(list, {:cont, acc}, reducer) ->
  reduce_list_cont(list, acc, reducer)
```

The hot loop state is `(list, acc, reducer)`. `reduce_list/3` is the public
state dispatcher; `reduce_list_step/3` dispatches each reducer output, routing
`:cont` back into `reduce_list_cont/3` and peeling `:halt`/`:suspend` out of the
hot path.

## Enum.reduce Shape

Public `Enum.reduce/3` is not the protocol callback. It is a small user-facing
wrapper over `Enumerable.reduce/3`: the public reducer returns the next
accumulator, and `Enum.reduce/3` wraps that value as `{:cont, acc}` for the
low-level protocol state machine before peeling `{:done, acc}` with
`reduce_finish/1`.

```text
Enum.reduce(enumerable, acc, reducer) ->
  reduce_finish(
    Enumerable.reduce(enumerable, {:cont, acc}, fn entry, inner_acc ->
      {:cont, reducer.(entry, inner_acc)}
    end)
  )
```

For a known list receiver, static protocol dispatch routes
`Enumerable.reduce/3` to `Enumerable.List.reduce/3`, and that implementation
delegates to the ordinary `List.reduce_cont/3` helper. Public `Enum` does not
carry separate list shortcuts; the protocol dispatch fact is the single route to
the implementation.

The first map-family layer (`fixtures/enum_map_family`) composes on that
tier-0 surface. Public functions such as `map/2`, `filter/2`,
`map_reduce/3`, `scan/2,3`, `map_every/3`, `map_join/2,3`, and
`map_intersperse/3` normalize the input through `to_list/1` and then call
module-local private builders. That keeps the public API small while still
exercising ordinary fz recursive list construction and return-demand lowering.
`with_index/2` has both Elixir shapes: integer offset and
`(entry, index) -> value` mapper; there is no public `with_index/3`. The mapper
overload is expressed as its own `@spec` arrow so same-name/same-arity overloads
preserve input/result correlation instead of collapsing those positions into
unions (see [`specs`](specs.md)).

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

Provider-library planning runs this rewrite over the linked working module, so
protocol callsites with a known receiver reach the protocol-owned
implementation module before native emission. A low-level `Enumerable.reduce/3`
`{:suspend, acc}` result is different: it is a real, materialized resumable
closure, a source-visible value rather than an internal continuation edge.

## Proof Gates

- `Enumerable.reduce(xs, {:cont, 0}, reducer)` enters `reduce_list_cont/3`
  directly from the dispatcher.
- `Enum.reduce(xs, 0, reducer)` is a public wrapper over `Enumerable.reduce/3`;
  static dispatch routes the known list receiver to `Enumerable.List.reduce/3`
  and then to local `List.reduce_cont/3`.
- A local known reducer lowers the hot list loop without the reducer-continuation
  trampoline.
- The protocol-first public path keeps `list_cons_allocs = 5` for the
  five-element input and currently allocates one native wrapper closure for the
  public reducer bridge.
- An opaque public reducer join stays closure-shaped, callable, and
  heap-continuation-free inside the protocol-dispatched list reducer path
  (`fixtures/opaque_fn_value_join`).
- `{:suspend, acc}` is a real materialized resumable closure.
- `Enum.count/1`, `Enum.member?/2`, and `Enum.reduce/3` keep their allocation
  floors (`fixtures/enum_list_allocations`: `list_cons_allocs = 5`,
  `closure_allocs = 1`, final heap headline `368` bytes).
- `foldl` and `map(double, xs)` (`fixtures/list_primitives`) keep their spec
  baseline (16 specs, 0 matchers) exercising cons-pattern dispatch and
  first-class fns passed in.
