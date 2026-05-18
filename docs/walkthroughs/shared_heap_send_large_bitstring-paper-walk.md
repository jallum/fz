# shared_heap_send_large_bitstring — paper walk under the proposed reducer

## The reducer rules

See `red-0-ast-eval-paper-walk.md`. Plus boundary rules.

## The source

```
fn child(bs) do
  send(1, bs)
end

fn main() do
  bs = <<1, 2, 3, ..., 70>>     # 70-byte bitstring literal
  spawn(fn () -> child(bs))
  print(receive())
end
```

Expected output: the same 70-byte bitstring.

## Process graph

```
   main (pid=1)
     |
     | bs := <<1..70>>   (compile-time literal)
     | spawn lambda(bs)  -> pid_child
     v
   child(bs) at pid_child
     send(1, bs)
     v
   main mbox <- bs
   print(receive()) -> bs
```

## Program roots

`main`, the spawned lambda.

## Root 1: `main`

| Step | Rule | Detail |
|---|---|---|
| 1.1 | fold-prim? / literal | `bs = <<1, 2, ..., 70>>` — the bitstring literal. Per README and `fz-q8d.2`, codegen const-folds the byte fields into a single `Prim::ConstBitstring` Descr. **From the reducer's viewpoint, `bs` is a literal Descr** of type `bitstring(70 bytes, content known)`. Bind `bs := bitstring_lit([1..70])`. |
| 1.2 | spawn with **static captures** | the lambda captures `bs`. Captures **are literal** (a const bitstring Descr). Per design: **static-capture spawn reduces the lambda body in isolation** with `bs` substituted. Lambda body becomes `child(bitstring_lit([1..70]))`. |
| | | The closure heap object dissolves into a static thunk. |
| 1.3 | (descend into spawned lambda — see Root 2) | |
| 1.4 | receive boundary | `receive()` opaque; into `print` extern. |

## Root 2: spawned lambda → `child(bs_lit)`

Reduce `child(bitstring_lit([1..70]))`:

| Step | Rule | Detail |
|---|---|---|
| 2.1 | dispatch | `child` one clause, head `(bs)`. Binds `bs := bitstring_lit([1..70])`. |
| 2.2 | substitute | body becomes `send(1, bitstring_lit([1..70]))`. |
| 2.3 | extern | `send` is an extern. Leave call in place. |

**Reduced lambda body:** `send(1, bitstring_lit([1..70]))`. The
`child` user fn dissolves entirely; its body merges into the lambda.

## Effect on the runtime

Per README: codegen emits the 70-byte payload and a 40-byte
`SharedBin` struct as static `.data`. The reduced lambda is a single
`fz_alloc_procbin_from_static` + `send` extern.

## Bodies emitted

| Fn | Bodies |
|---|---|
| `main` | 1 |
| lambda | 1 |
| `child` | **0** (dissolved into the lambda) |

## Findings

**The reducer treats large bitstring literals as literal Descrs.**
Once `ir_fold` (fz-q8d.2) has collapsed the byte fields into a
`Prim::ConstBitstring`, the reducer sees a literal Descr just like
`int_lit(42)`. Substitution, dispatch, and static-capture inlining
all work normally. **The reducer does not touch bitstring contents** —
it treats the literal as an opaque-blob-but-statically-known Descr.

**Static-capture spawn dissolves the `child` user fn.** Because `bs`
is a literal at the spawn site, the lambda body `child(bs)` reduces
fully through one substitution step, eliminating `child` from the
emitted bodies.

**Bitstring size threshold is a codegen concern, not a reducer
concern.** The 64-byte `SHARED_BIN_THRESHOLD_BYTES` cutoff lives in
codegen (`procbin::*`). The reducer is path-agnostic and produces the
same reduced Module regardless. Interp routes through
`Heap::alloc_bitstring`; JIT/AOT use the static `.data` SharedBin.
Three-path parity preserved by construction.

**Bitstring construction at runtime would be a boundary.** If `bs`
were built dynamically (e.g. from a user input or a concat with an
opaque part), the reducer would stop at the construction site and
emit code for it. The fixture's static literal is the easy case.

**No judgment calls surfaced.** Mechanical walk.
