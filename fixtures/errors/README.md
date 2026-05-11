# Diagnostic fixtures

Each subdirectory is one fixture. Convention:

```
fixtures/errors/<name>/
    input.fz       # fz source that produces a known diagnostic
    expected.txt   # the rendered diagnostic, byte-for-byte (NO_COLOR)
```

Fixtures land progressively as the fz-ul4.20 arc fills in:

- .20.1 — directory exists; no fixtures yet (no renderer to compare against).
- .20.6 — renderer fixtures land here. Synthetic diagnostics drive the
  snapshot tests for layout, multi-span, lineage, tabs, DUMMY spans.
- .20.7 — end-to-end fixtures: real fz source that produces a lex /
  parse / resolve / macro / lower / type / runtime diagnostic, with the
  rendered output captured exactly. These run via `cargo test` under
  `tests/diag/`.
- .20.8 — type-rendering fixtures: programs with provably-unreachable
  branches; the expected output includes the rendered set-theoretic
  type vocabulary.

Tests set `NO_COLOR=1` so golden files stay plain text.
