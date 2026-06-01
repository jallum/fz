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
