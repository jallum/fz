# Golden CLIF fixtures (fz-ul4.32)

A handful of fixtures have checked-in **golden CLIF** files — exact
snapshots of what `fz dump --emit clif <fixture>` produces. The test
`golden_clif` in `tests/fixture_matrix.rs` dumps each fixture that has an
`expected.clif` sidecar and diffs it against the committed file. Drift →
test failure with the diff inline.

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

The golden set is opt-in: any fixture with `expected.clif` participates in
`golden_clif`, and any fixture with `expected.specs` participates in
`golden_specs`. Matcher-heavy receive fixtures usually carry `budget.*`
README frontmatter instead, which checks output shape without committing
thousands of generated lines.

## Workflow

### Running the test

```
cargo test --workspace golden_clif
```

Passes when every fixture with an `expected.clif` sidecar matches its
source's current CLIF output. Fails otherwise with the full diff and the
bless instruction.

### Blessing (intentional updates)

```
BLESS=1 cargo test --workspace golden_clif
```

Rewrites every golden from actual output. **Bless is a deliberate
act** — review the diff in the resulting commit. Don't bless to silence
a test you don't understand; investigate first.

### Adding a fixture to the golden set

1. Create `fixtures/<name>/expected.clif`.
2. Run `BLESS=1 cargo test --workspace golden_clif` to seed it.
3. Commit the new `.clif`. The first commit pins the status quo.

### Removing a fixture from the golden set

Delete the `.clif` file. If the fixture still needs broad shape coverage,
add or keep `budget.*` fields in the fixture README frontmatter.

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

## Why golden files instead of spot-check directives?

`expect_clif_contains: count_s2: iadd` is fine for "does this instruction
appear anywhere." A full golden is better when we need exact review signal,
but README budget frontmatter is better when the main concern is compiler
shape drift. It checks telemetry emitted by the compiler:

- `budget.codegen.min_functions`
- `budget.codegen.max_functions`
- `budget.codegen.min_instructions`
- `budget.codegen.max_instructions`
- `budget.specs.min_count`
- `budget.specs.max_count`

A full golden can answer:

- Is anything *unexpected* in the output?
- Did the structure shift in a way the assertion didn't anticipate?
- What changed between this commit and the last one?

A golden file answers all three by construction. Budgets answer the cheaper
question: "did this fixture get unexpectedly huge or unexpectedly tiny?"
For matcher-heavy fixtures, prefer telemetry counters over pretty-printer
proxies. `specs.*_count` checks the typer's emitted `spec_count`
measurement. `codegen.*_functions` and `codegen.*_instructions` check the
`fz.codegen.function_lowered` events emitted when codegen lowers fz spec
bodies and receive helper bodies. The matching `fz.codegen.lower_function`
span events also carry per-body timing in JSON telemetry logs.

## Out of scope

- Golden assembly / final machine code (the post-Cranelift-opt output).
  CLIF is what we emit; ASM is what runs. CLIF golden catches the
  changes we control directly; ASM goldens would catch Cranelift
  version drift. Worth doing eventually as a separate measurement.
- Microbenchmarks. CLIF shape is one signal; runtime cost is another.
- Auto-blessing on CI. Bless stays manual — the deliberate human gate
  is the point.
