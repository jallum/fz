---
purpose: "Enum map-family functions match Elixir while exposing one-pass list builders to native return-demand lowering"
paths: [jit, interp, aot, repl]
oracle: oracle.exs
timeout.interp_secs: 15
timeout.repl_secs: 15
---

Exercises the `fz-g58.24` Enum map family:
`map/2`, `filter/2`, `reject/2`, `flat_map/2`, `map_reduce/3`, `scan/2,3`,
`intersperse/2`, `with_index/1,2`, `map_every/3`, `map_join/2,3`, and
`map_intersperse/3`.

`with_index/2` covers both Elixir shapes: integer offset and function mapper.
The mapper cases intentionally return strings, integers, and tuples so the
fixture proves same-name/same-arity overload selection preserves the selected
arrow's input-to-output correlation. `map_every/3` covers the `0`, `1`, and
`> 1` step cases.

The interp/repl timeout overrides keep correctness coverage while `fz-g58.52`
owns restoring the default fixture gate.
