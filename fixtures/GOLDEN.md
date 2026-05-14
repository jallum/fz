# Golden CLIF fixtures (fz-ul4.32)

A handful of fixtures have checked-in **golden CLIF** files — exact
snapshots of what `fz dump --emit clif <fixture>` produces. The test
`golden_clif` in `tests/fixture_matrix.rs` dumps each one and diffs it
against the committed `.clif` file. Drift → test failure with the diff
inline.

This is the diff machine that makes every codegen change legible:

- An intended optimization (e.g., remove a tag/untag round-trip at the
  cont seam) shows up as a precise CLIF diff. Reviewers see exactly
  which instructions disappeared.
- An accidental regression in some unrelated commit shows up as a
  golden test failure in a fixture you weren't even touching. Caught
  immediately, traced to the commit responsible.
- The acceptance criterion for any codegen optimization can be stated
  as "the golden for fixture X should match the form Y."

## Current golden set

See `GOLDEN_FIXTURES` in `tests/fixture_matrix.rs`. As of fz-ul4.32:

- `add1.fz` — smallest round-trip
- `tail_recursion.fz` — §8.1 cps-in-clif acceptance
- `higher_order.fz` — §8.2
- `closure_typed_captures.fz` — §8.3
- `concurrency_ping_pong.fz` — §8.4

## Workflow

### Running the test

```
cargo test --workspace golden_clif
```

Passes when every golden in `GOLDEN_FIXTURES` matches its source's
current CLIF output. Fails otherwise with the full diff and the bless
instruction.

### Blessing (intentional updates)

```
BLESS=1 cargo test --workspace golden_clif
```

Rewrites every golden from actual output. **Bless is a deliberate
act** — review the diff in the resulting commit. Don't bless to silence
a test you don't understand; investigate first.

### Adding a fixture to the golden set

1. Append the fixture's filename to `GOLDEN_FIXTURES` in
   `tests/fixture_matrix.rs`.
2. Run `BLESS=1 cargo test --workspace golden_clif` to seed the
   `fixtures/<stem>.clif` file.
3. Commit the new `.clif` alongside the test list change. The first
   commit pins the status quo.

### Removing a fixture from the golden set

Drop it from `GOLDEN_FIXTURES`. Delete the `.clif` file. Done.

## Determinism

CLIF output is deterministic for a fixed Cranelift version + fixed
codegen logic. Sources of non-determinism we've seen and handled:

- **Spec IDs** (e.g., `_s2`, `_s7`): assigned in source order by the
  typer's spec registry. Stable.
- **Value numbers** (`v0`, `v1`, ...): SSA-deterministic from
  Cranelift. Stable.
- **FuncId numbering** (`u0:N`): driven by `compile_with_backend`'s
  declaration order. Stable.

If a future change introduces non-determinism (e.g., HashSet iteration
order leaking into emitted IR), either:

- Fix it at the source (use BTreeSet / sort before consuming), OR
- Normalize the diff in the test before comparison.

The first is preferred.

## Why this instead of expect_clif_contains?

`expect_clif_contains: count_s2: iadd` is fine for "does this
instruction appear anywhere." It cannot answer:

- Is anything *unexpected* in the output?
- Did the structure shift in a way the assertion didn't anticipate?
- What changed between this commit and the last one?

A golden file answers all three by construction. The legacy
`expect_clif_*` directives in fixture headers stay for now as
belt-and-braces — they pin specific invariants in human-readable form.
For new acceptance criteria, prefer adding a fixture to the golden set
over writing more spot-check directives.

## Out of scope

- Golden assembly / final machine code (the post-Cranelift-opt output).
  CLIF is what we emit; ASM is what runs. CLIF golden catches the
  changes we control directly; ASM goldens would catch Cranelift
  version drift. Worth doing eventually as a separate measurement.
- Microbenchmarks. CLIF shape is one signal; runtime cost is another.
- Auto-blessing on CI. Bless stays manual — the deliberate human gate
  is the point.
