# Type-specialization corpus (spike)

The minimal programs the `fz-g58.65` inference engine is built against. Each is a
*measuring stick* for `.agent/docs/type-specialization.md`: the program plus the
type the model says it must infer. The engine is correct when every program here
settles to its stated type.

These are not fixtures (no `expected.txt`, no four-path matrix) — they exercise
the planner's type inference, not runtime behavior, so they live outside
`fixtures/`.

## The corpus and what the model infers

| program | shape | `myreduce`/`add` infers | current planner |
| --- | --- | --- | --- |
| `add.fz` | `a + b` | `(number, number) -> number`; `add(1,2) : int` | settles ✓ |
| `fold_tail.fz` | tail-recursive fold, empty-capture closure | `number` | settles ✓ |
| `fold_nontail.fz` | non-tail wrapper over the fold | `number` | settles ✓ |
| `fold_capture_int.fz` | threaded closure captures an `int` | `number` | settles ✓ |
| `fold_capture_closure.fz` | threaded closure captures **another closure** | `number` | **diverges (4096)** |
| `fold_state_machine.fz` | `{:cont}\|{:halt}` state + nested closure (the `Enum.reduce` shape) | `number` | **diverges (4096)** |

The discriminator is the captured value's type: an `int` capture (`&f[5]`) settles;
a closure capture (`&f[&g…]`) is the one the current planner can't reach a fixpoint
on. Under the model a captured closure is a concrete capture like any other — it is
the bug these last two programs pin.
