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
| `match_nested_binding.fz` | tuple payload is a cons pattern returning `h` | `main() : {int, :error}`; composed tuple and list evidence carries nested binding type into the selected leaf | not pinned |
| `enum_count.fz` | `Enum.count/1` over a List receiver | `Enum.count([1,2,3]) : int`; protocol dispatch reaches the List count callback | settles ✓ |
| `enum_reduce.fz` | `Enum.reduce/3` over a List receiver with an inline reducer | `Enum.reduce([1,2,3], 0, +) : int`; public wrapper, protocol dispatch, and list loop converge | settles ✓ |
| `enum_reduce_named_ref_ok.fz` | `Enum.reduce/3` over a List receiver with `&Main.reducer/2` | `Enum.reduce([1,2,3], 0, &Main.reducer/2) : int`; named reducer references converge like inline closures | settles ✓ |
| `enum_reduce_range.fz` | `Enum.reduce/3` over a Range receiver | `Enum.reduce(1..3, 0, +) : int`; protocol dispatch must target the Range impl | target; not pinned |
| `enum_reduce_named_ref.fz` | ill-typed named reducer returns protocol control tuples to public `Enum.reduce/3` | diagnostic: `+` is not defined for a tuple accumulator; no `Unknown`/`any` fallback | target; intentionally not pinned |
| `fold_tail.fz` | tail-recursive fold, empty-capture closure | `number` | settles ✓ |
| `fold_nontail.fz` | non-tail wrapper over the fold | `number` | settles ✓ |
| `fold_capture_int.fz` | threaded closure captures an `int` | `number` | settles ✓ |
| `fold_capture_closure.fz` | threaded closure captures **another closure** | `number` | **diverges (4096)** |
| `fold_state_machine.fz` | `{:cont}\|{:halt}` state + nested closure (the `Enum.reduce` shape) | `number` | **diverges (4096)** |

## Target Backlog

These targets are committed source examples, not executable assertions yet.
Promote them one at a time so each commit isolates one missing capability.

| program | target capability |
| --- | --- |
| `match_nested_partition.fz` | Preserve nested tuple/list partition evidence across sibling arms. |
| `match_tuple_tag_partition.fz` | Partition same-arity tuples by atom tag and project the matching payload. |
| `match_tuple_arity_partition.fz` | Partition tuples by arity without leaking impossible fields into joins. |
| `match_guard_partition.fz` | Treat guards as refinement evidence before selecting a clause body. |
| `match_map_binding.fz` | Bind fields from map patterns while preserving the callable parameter surface. |
| `enum_reduce_range.fz` | Devirtualize protocol dispatch through the Range receiver type. |
| `enum_reduce_named_ref.fz` | Stop on a proved invalid reducer accumulator and emit a diagnostic. |

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

`match_nested_binding.fz` composes the tuple and list cases: `{:ok, [h | _]}`
first narrows/project the tuple payload, then narrows that payload to a non-empty
list so `head(payload)` flows `int` into the leaf.
