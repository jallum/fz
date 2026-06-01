# Type-specialization corpus (spike)

The minimal programs the `fz-g58.65` inference engine is built against. Each is a
*measuring stick* for `.agent/docs/type-specialization.md`: the program plus the
type the model says it must infer. The engine is correct when every program here
settles to its stated type.

These are not fixtures (no `expected.txt`, no four-path matrix) — they exercise
the planner's type inference, not runtime behavior, so they live outside
`fixtures/`.

## The corpus and what the model infers

| program | shape | inferred result | current planner |
| --- | --- | --- | --- |
| `add.fz` | `a + b` | `(number, number) -> number`; `add(1,2) : int` | settles ✓ |
| `poly_id.fz` | same `FnId` called at `int` and `:ok` | `main() : {int, :ok}`; independent activations do not over-join | settles ✓ |
| `poly_named_ref.fz` | same zero-capture call-target value applied at `int` and `:ok` | `main() : {int, :ok}`; named refs do not collapse activations into one monomorphic cell | settles ✓ |
| `poly_named_ref_pattern.fz` | named ref to a source-total pattern fn applied at two atom literals | `main() : {:one, :two}`; call-target activation still drives matcher proof and keeps the catch-all dead | settles ✓ |
| `poly_capture_ref.fz` | same captured closure value applied at `int` and `:right` | `main() : {{:ok, int}, {:ok, :right}}`; captures are inference inputs, not callable arity | settles ✓ |
| `match_atom_partition.fz` | same multi-clause `FnId` called with different atom literals | `main() : {:one, :two}`; matcher proof selects different leaves per activation | settles ✓ |
| `match_list_partition.fz` | same multi-clause `FnId` called with `[]` and `[1]` | `main() : {:empty, :cons}`; list-shape proof selects empty vs cons leaves per activation | settles ✓ |
| `match_list_binding.fz` | cons clause returns `[h | _]` binding | `main() : {:empty, int}`; matcher-produced bindings carry element type into the selected leaf | settles ✓ |
| `match_tuple_binding.fz` | tuple clause returns `{:ok, x}` binding | `main() : {int, :error}`; tuple-shape proof and field projection carry payload type into the selected leaf | settles ✓ |
| `match_nested_binding.fz` | tuple payload is a cons pattern returning `h` | `main() : {int, :error}`; composed tuple and list proof carries nested binding type into the selected leaf | settles ✓ |
| `match_nested_partition.fz` | tuple payload partitions empty-list, cons-list, and atom leaves | `main() : {:empty, int, :error}`; nested sibling arms remain distinct per activation | settles ✓ |
| `match_tuple_tag_partition.fz` | same-arity tuple clauses with different atom tags | `main() : {int, :bad}`; tag proof chooses the matching payload projection | settles ✓ |
| `match_tuple_arity_partition.fz` | tuple clauses with different arities and a non-tuple arm | `main() : {int, {int, int}, :other}`; arity proof keeps impossible fields out of joins | settles ✓ |
| `match_guard_partition.fz` | tuple pattern with a guard helper over the payload | `main() : {int, :fallback}`; literal proof selects the guarded arm without exposing singleton return types | settles ✓ |
| `match_map_binding.fz` | map clause binds `%{id: x}` | `main() : {int, :none}`; matcher-map hit/miss proof carries the field value and skips the catch-all | settles ✓ |
| `enum_count.fz` | `Enum.count/1` over a List receiver | `Enum.count([1,2,3]) : int`; protocol dispatch reaches the List count callback | settles ✓ |
| `enum_reduce.fz` | `Enum.reduce/3` over a List receiver with an inline reducer | `Enum.reduce([1,2,3], 0, +) : int`; public wrapper, protocol dispatch, and list loop converge | settles ✓ |
| `enum_reduce_named_ref_ok.fz` | `Enum.reduce/3` over a List receiver with `&Main.reducer/2` | `Enum.reduce([1,2,3], 0, &Main.reducer/2) : int`; named reducer references converge like inline closures | settles ✓ |
| `enum_reduce_range.fz` | `Enum.reduce/3` over a Range receiver | `Enum.reduce(1..3, 0, +) : int`; struct receiver dispatches to the Range impl | settles ✓ |
| `enum_reduce_named_ref.fz` | ill-typed named reducer returns protocol control tuples to public `Enum.reduce/3` | diagnostic: `+` is not defined for a tuple accumulator; no `Unknown`/`any` fallback | diagnostic ✓ |
| `fold_tail.fz` | tail-recursive fold, empty-capture closure | `number` | settles ✓ |
| `fold_nontail.fz` | non-tail wrapper over the fold | `number` | settles ✓ |
| `fold_capture_int.fz` | threaded closure captures an `int` | `number` | settles ✓ |
| `fold_capture_closure.fz` | threaded closure captures **another closure** | `number` | settles ✓ |
| `fold_state_machine.fz` | `{:cont}\|{:halt}` state + nested closure (the `Enum.reduce` shape) | `number` | settles ✓ |

## Target Backlog

No target-only spike programs are currently committed. Add source examples here
first, then promote them one at a time so each commit isolates one missing
capability.

The discriminator is the captured value's type: an `int` capture (`&f[5]`) settles;
a closure capture (`&f[&g…]`) is concrete in the same way. Under the model a
captured closure is just another captured value, and the pinned fold tests keep
that invariant from regressing.

`poly_id.fz` pins the next model boundary: `FnId` is body/callable identity, not
the inference instance. The same `id` body is activated twice, once at `int` and
once at `:ok`; callers read their own activation's return instead of a single
joined `int | :ok` function cell.

`poly_named_ref.fz` moves the same boundary through a call-target value:
`&id/1` has no captures, but it is still a value whose two applications must read
separate activations keyed by their arguments. The current production planner's
body dump still shows the obsolete shape (`any` plus one narrow spec); the pinned
side-engine assertion is the guardrail for the transplant.

`poly_named_ref_pattern.fz` adds the pattern matcher to that call-target path.
The source is total via a catch-all, but the two observed activations should
select only the `:left` and `:right` leaves; the catch-all is dead for this
callsite and should not contribute `:other`.

`poly_capture_ref.fz` proves captures are only inference inputs. The closure body
receives `tag` as a leading lowered parameter, but the closure value is still
callable with one explicit parameter; applying the same closure at `int` and
`:right` should produce two activation reads with the same captured `:ok`.

`match_atom_partition.fz` pins the pattern-dispatch boundary: the same lowered
decision tree is evaluated under each activation's input facts. The case returns
atom literals rather than integer literals so the test isolates matcher leaf
selection from the separate finite-height rule that widens distinct integer
literals to `int`.

`match_list_partition.fz` takes the same boundary through structural list tests:
non-empty list literals carry `nonempty_list(T)`, so `is_nil` and `is_list_cons`
can prune the matcher tree to the empty or cons leaf without re-running analysis.

`match_list_binding.fz` proves the selected cons leaf receives the pattern
binding itself: the lowered `head(list)` primitive projects `int` from the
non-empty input list, so the leaf returns `int` rather than an unbound or
over-joined value.

`match_tuple_binding.fz` runs the same binding-flow check through tuple matcher
tests. The lowered `type_test` and `tuple_field` proof narrows `{:ok, int}`
to the tuple leaf and projects the payload without letting the atom leaf or
impossible tuple arities contribute.

`match_nested_binding.fz` composes the tuple and list cases: `{:ok, [h | _]}`
first narrows/project the tuple payload, then narrows that payload to a non-empty
list so `head(payload)` flows `int` into the leaf.

`match_nested_partition.fz` adds the sibling empty-list arm to the same nested
shape. The empty payload, cons payload, and atom fallback are three distinct
activations; the catch-all clause is present to keep the source total but should
not contribute to the observed `main/0` return.

`match_tuple_tag_partition.fz` keeps tuple arity constant and varies only the
first atom field. The selected clause projects the second field from the matching
tag, so the `:ok` activation returns `int` while the `:error` activation returns
`:bad`.

`match_tuple_arity_partition.fz` varies tuple arity instead of tag. The one-field
and two-field tuple arms project different payload shapes, while the atom arm
stays disjoint; impossible tuple arities must not contribute `any` or extra
fields to the result.

`match_guard_partition.fz` adds guard selection without changing visible payload
types. The tuple payload from `{:ok, 1}` is typed as `int`, but it still carries
literal proof through tuple projection so `positive(x)` can prove the guard
true; `{:ok, 0}` proves it false and reaches the fallback.

`match_map_binding.fz` takes the same proof channel through map-pattern lowering.
The lowered matcher performs `matcher_map_get(map, :id)` and then
`is_matcher_map_miss(value)`; static-key map construction proves the hit for
`%{id: 1}`, carries the `id` value proof into the selected leaf, and lets `:none`
take the atom clause without the catch-all contributing to `main/0`.

`enum_reduce_range.fz` extends protocol dispatch to schema-backed struct
receivers. `1..3` lowers through `Range.new/3` to `%Range{...}`, which the engine
types as the existing opaque `impl-target::Range` value while carrying
field-wise proof for `first`, `last`, and `step`. Protocol devirtualization then
chooses `Enumerable.Range.reduce/3`, and struct-field projection feeds the Range
callback enough type information for public `Enum.reduce/3` to settle to `int`.
