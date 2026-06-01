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
| `poly_id.fz` | same `FnId` called at `int` and `:ok` | `main() : {int, :ok}`; independent activations do not over-join | not pinned |
| `match_atom_partition.fz` | same multi-clause `FnId` called with different atom literals | `main() : {:one, :two}`; matcher evidence selects different leaves per activation | not pinned |
| `match_list_partition.fz` | same multi-clause `FnId` called with `[]` and `[1]` | `main() : {:empty, :cons}`; list-shape evidence selects empty vs cons leaves per activation | not pinned |
| `match_list_binding.fz` | cons clause returns `[h | _]` binding | `main() : {:empty, int}`; matcher-produced bindings carry element type into the selected leaf | not pinned |
| `match_tuple_binding.fz` | tuple clause returns `{:ok, x}` binding | `main() : {int, :error}`; tuple-shape evidence and field projection carry payload type into the selected leaf | not pinned |
| `fold_tail.fz` | tail-recursive fold, empty-capture closure | `number` | settles ✓ |
| `fold_nontail.fz` | non-tail wrapper over the fold | `number` | settles ✓ |
| `fold_capture_int.fz` | threaded closure captures an `int` | `number` | settles ✓ |
| `fold_capture_closure.fz` | threaded closure captures **another closure** | `number` | **diverges (4096)** |
| `fold_state_machine.fz` | `{:cont}\|{:halt}` state + nested closure (the `Enum.reduce` shape) | `number` | **diverges (4096)** |

The discriminator is the captured value's type: an `int` capture (`&f[5]`) settles;
a closure capture (`&f[&g…]`) is the one the current planner can't reach a fixpoint
on. Under the model a captured closure is a concrete capture like any other — it is
the bug these last two programs pin.

`poly_id.fz` pins the next model boundary: `FnId` is body/callable identity, not
the inference instance. The same `id` body is activated twice, once at `int` and
once at `:ok`; callers read their own activation's return instead of a single
joined `int | :ok` function cell.

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
tests. The lowered `type_test` and `tuple_field` evidence narrows `{:ok, int}`
to the tuple leaf and projects the payload without letting the atom leaf or
impossible tuple arities contribute.
