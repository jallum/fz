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
  `QuotedSourceRoot::semantically_eq(&other, Horizon)` — a two-sided lockstep
  walk over both graphs that fast-fails at the first difference. No canonical
  rendering or digest is ever materialized.

## Why The Split Matters

- `{heap, root}` answers "which quoted source root is this?"
- `semantically_eq` answers "do these roots contain the same source shape?"
- A rebuilt equivalent graph on a different heap gets a different key but
  compares semantically equal — atoms compare by rendered name, not id, so the
  walk is cross-heap stable.
- `Horizon` selects how deep the comparison descends:
  `Horizon::Full` compares to the leaves (function identity — the body is part
  of the definition), `Horizon::Surface` skips each `do:` body (module/code
  identity — bodies belong to their own per-function facts, so a body-only
  edit leaves the surface unchanged).
- Compiler2 uses that split deliberately:
  code/module source revisions compare at `Horizon::Surface`,
  function-definition revisions compare at `Horizon::Full`. Transport identity
  (a fresh heap from a re-parse) never bumps a revision by itself.

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
- Postfix bracket access quotes through an Elixir-shaped `Access.get` remote
  callee form.
- `cond do` quotes through ordinary `{:cond, meta, [[do: [{:->, ...}, ...]]]}`.
  structure.
- Capture refs cover local names, remote names, and bare/operator refs such as
  `&Kernel.+/2` and `&+/2`.
- Extern-symbol folding for adjacent `ident::ident` names is only valid in
  ordinary expression/capture position. Bitstring segment parsing suppresses
  that folding so forms like `payload::binary-size(len)` stay quoted as
  segment/type AST, not as fake extern-symbol variables.

## Surface Grouping

- Raw quoted source still preserves one top-level form per source clause.
- Compiler2 function surfaces are then composed back into first-class grouped
  quoted roots on that same heap:
  a logical function surface is a quoted list carrying attached `@doc` /
  `@spec` items plus every grouped `fn` / `fnp` / `defmacro` clause, or a
  single `extern` item surface.
- Grouping is by `{name, arity}` and flushes at the same non-function
  boundaries the legacy item surface exposes.
- Grouped roots are interned per quoted-source heap. Re-reading the same body
  must yield the same `{heap, root}` for the same logical function surface.
- Protocol-impl callback bodies use that same grouped-root substrate; they are
  not a second special-case function source format.
- `FactKey::FunctionSource(FunctionId)` is now the lazy authoritative function
  fact. Source jobs note grouped quoted roots first; `FunctionDefined` is
  derived on demand from that fact.
- `FunctionDefined` now carries a compiler2-owned `FunctionSurface` decoded
  from grouped quoted source. Source-defined functions and generated lambdas
  both use that same callable-surface model.
- The noted function-source fact must carry enough callable surface to keep
  pre-definition name resolution honest. Today that explicitly includes the
  variadic bit, because lowering may need callable matching before
  `FunctionDefined` exists.

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

- `__fz_lexical__`: stable lexical context; semantic content, compared by
  `semantically_eq`.
- `__fz_span__`: diagnostic-only span payload; not semantic content, skipped
  by `semantically_eq`.
- `__fz_namespace_id__`: transport-only namespace handle; not semantic
  content, skipped by `semantically_eq`.

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

## Discovery Authority

- `QuotedCodeSource` now carries two compiler2-owned views of one source
  submission:
  the authoritative quoted root and a derived `ScopeSurface` read model.
- `ScopeSurface` is intentionally narrow:
  top-level attrs plus decoded scope forms for `alias`, `import`, `require`,
  functions, modules, protocols, protocol impls, structs, and macro-call
  surface forms.
- Code/module/protocol discovery facts read those decoded forms directly from
  quoted roots; they no longer store or zip against old parser `Rc<Item>`
  payloads.
- Module bodies and protocol bodies use the same `ScopeSurface` shape as
  top-level code, so nested discovery and protocol-impl callback discovery stay
  in one quoted-source world.
- Function bodies, contracts, and dispatch planning now read compiler2-owned
  `FunctionSurface` data directly rather than old parser function records.

## Rooting Contract

- `QuotedSourceRoot` retains the owning `QuotedSourceHeap` by `Rc`, so the
  heap outlives the `AnyValueRef`.
- The raw `AnyValueRef` is never treated as durable without its heap owner.
- Runtime bitstring/procbin readers operate on heap-object words
  (`AnyValueRef::heap_object_word()`), not `AnyValueRef::raw_word()`.
- Quoted graphs are built bottom-up on an immutable heap, so they are acyclic
  by construction. The semantic walk treats unsupported runtime-only value
  kinds as a structural error, which `semantically_eq` reports conservatively
  as "not equal" (forcing a revision bump rather than risking a missed change).
