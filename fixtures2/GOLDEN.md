# Fixture Conventions

A fixture is a small `.fz` program under `fixtures2/behavior/` that proves one
language claim. Each applicable fixture runs through the `run`, `interp`, and
`build` paths. A filename route prefix or an explicit `defer.<path>:` entry may
narrow those paths.

See `.agent/docs/fixtures.md` for discovery, frontmatter, pass/fail, and BLESS
mechanics. This file defines which assertion medium owns a fixture claim.

## Assertion media

Choose the most direct observable boundary for the fixture purpose:

1. **In-language assertion** — use `assert` or `refute` when the claim is a
   value or boolean invariant. This is the default for behavior.
2. **Rendering golden** — use `dbg` plus `expected.txt` only when the rendered
   string is itself the artifact under test.
3. **Memory-floor stats** — use `Process.heap_alloc_stats()` plus path-specific
   goldens for allocation counts that differ between interpreter and native
   execution.
4. **Expect-failure** — use `expect: abort` or `expect: diagnostic` plus the
   corresponding diagnostic contract when the language must reject or abort.
5. **Compiler contract** — use `assert.metric.*`, `assert.edge`, or a canonical
   snapshot when the claim concerns compiler structure rather than program
   behavior.

One fixture may need two media when it makes two independent claims, such as a
runtime result and an allocation floor. Do not use rendered output as a proxy
for a value assertion, and do not add runtime assertions to a fixture whose
purpose is compiler shape: the assertion would alter the artifact being
measured.

## Sidecars

The matrix recognizes these sibling artifacts:

```text
<name>.expected.txt
<name>.expected.<path>.txt
<name>.expected.diagnostics
<name>.expected.<path>.diagnostics
<name>.expected.stderr
<name>.expected.<path>.stderr
<name>.oracle.exs
```

`<path>` is `run`, `interp`, or `build`. A missing stdout or diagnostic golden
means the corresponding output must be empty.

## Source comments

The `purpose:` frontmatter line is the fixture headline. Optional comments
below the frontmatter should add a mechanism or rationale that the purpose does
not already state. Write current facts in present tense; do not preserve
migration chronology or duplicate the fixture code in prose.

## Compiler-shape contracts

Compiler structure is observed through compiler2-owned authorities:

- `assert.metric.<name>:` pins a numeric compiler invariant;
- `assert.edge:` pins a semantic call edge;
- `snapshot.call_edges:` names a dense canonical call-edge snapshot;
- explicit dump artifacts may pin a representation whose text is contractual.

Shape contracts must name a current compiler2 fact or artifact. Historical
planner and codegen counters are not translated into new metrics unless a
current invariant and consumer justify them.

## Updating expected output

`BLESS=1 cargo test --test fixture_matrix` updates current stdout and diagnostic
goldens. Oracle-backed fixtures take their shared `expected.txt` from the
declared Elixir script. Review every changed artifact before committing; BLESS
records observed output but does not decide that the output is correct.
