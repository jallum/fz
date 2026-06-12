# Legacy runtime-library snapshot

`kernel.fz` and `runtime.fz` as they were before fz-rh2.18.5 (commit
2de4b1a87~1). The old pipeline's parser cannot read the current surface
(ascribed operator-clause params like `fn left :: integer + right :: integer`),
and the old pipeline never consumes those clauses; it loads this pair instead.
The two files are only consistent together: the current `runtime.fz` imports
comparison operators this kernel does not export.

Read exclusively by the old pipeline's entry points in
`src/modules/runtime_library.rs` (`legacy_source` / `legacy_prelude_source`).
Compiler2 reads only the current sources.

Deleted with the old pipeline: fz-rh2.16.6.1.
