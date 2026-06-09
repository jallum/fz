# Quoted Source

`src/compiler2/source.rs` is the compiler2-owned quoted-source substrate for
the `fz-rh2.11.7.*` arc.

## What It Owns

- One source graph lives on one Fz `Process` heap, carried as runtime-shaped
  values only: atoms, lists, tuple structs, maps, and bitstrings.
- A source root is an `AnyValueRef` into that heap.
- The durable source key is `{heap, root}`:
  `QuotedSourceKey { heap_id, root }`.
- Structural comparison is separate:
  `QuotedSourceFingerprint { policy, digest, canonical }`.

## Why The Split Matters

- `{heap, root}` answers "which quoted source root is this?"
- The fingerprint answers "what quoted source shape does this root contain?"
- A rebuilt equivalent graph on a different heap gets a different key and the
  same semantic fingerprint.

That keeps identity honest and still gives compiler2 a stable semantic
comparison surface when it wants one.

## Source Shape

- AST nodes are Elixir-shaped 3-tuples:
  `{head, meta_map, tail}`.
- Most calls use an atom head and `tail = [arg, ...]`.
- Remote calls and closure calls are allowed to carry a quoted callee AST in
  `head`, not just an atom.
- Variables use `tail = lexical_context_map`.
- Module aliases use `{:__aliases__, meta, [:Foo, :Bar]}`.
- Keyword items are ordinary 2-tuples inside lists.
- FZ `extern` items are quoted as `{:extern, meta, [abi_binary, options_map]}`.
  `options_map` currently carries raw source strings for `name`, `params`,
  `return`, optional `when`, and `variadic`.

## Bootstrap Coverage

- `src/compiler2/frontdoor.rs` now quotes the compiler-owned bootstrap/runtime
  surface directly, including:
  `extern`,
  runtime-prelude operator import filters such as `only: [+: 2]`,
  `if`,
  `receive ... after`,
  and anonymous `fn ... end`.
- Runtime library sources are expected to reach quoted roots without an old-AST
  fallback path.

## Private Metadata Keys

- `__fz_lexical__`: stable lexical context for semantic comparison.
- `__fz_span__`: diagnostic-only span payload; included only under the
  diagnostic fingerprint policy.
- `__fz_namespace_id__`: transport-only namespace handle; excluded from every
  fingerprint policy.

## Scope Authority

- Compiler2 does not maintain a second mutable compile-env store for quoted
  source.
- `ScopeSnapshot` is the one scope projection carrier:
  `{module_id, namespace_head, function_id?}`.
- `World::scope_lexical_context` derives quoted lexical metadata from that
  snapshot.
- `World::project_module_value` and `World::project_env_value` project
  `__MODULE__` / `__ENV__` as Fz-shaped values from the same snapshot.
- The namespace id carried in quoted metadata is transport only; it helps jobs
  and tests line contexts back up with the live namespace chain, but it is not
  semantic identity.

## Rooting Contract

- `QuotedSourceRoot` retains the owning `QuotedSourceHeap` by `Rc`, so the
  heap outlives the `AnyValueRef`.
- The raw `AnyValueRef` is never treated as durable without its heap owner.
- The fingerprint walk rejects cycles and unsupported runtime-only value kinds.
