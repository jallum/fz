# Targets

Target versions of agent docs: subsystem models written as if the work is already
done, in the same present-tense voice as `.agent/docs/`. Each file here mirrors a
doc (or names a subsystem that has no doc yet) and describes the **finished** shape.

The split is deliberate. `.agent/docs/` says what the code does today.
`.agent/targets/` says what it is being built toward. When a target is made real,
its file moves into `.agent/docs/` and replaces the doc it mirrors — so a target is
written so that the move is a straight swap, no rewrite.

Read a target to learn the destination; read the matching `.agent/docs/` file to
learn where the code stands.

## What these targets describe

One change, seen from several subsystems: **representing a type and naming a type
are separate jobs.**

- `Types` represents — it mints and compares set-theoretic symbols and is ignorant
  of what the language calls them. A symbol carries its own content, so the lattice
  never consults a name table.
- Naming is reference and definition — a source name resolves through the namespace
  to an identity, and the identity resolves to a hard `Ty` as a fact the work graph
  settles like any other.

The current code blurs the two: it re-derives a per-call name→type table by
re-lexing runtime source, and it recovers a symbol's content by looking its name up
in a side map threaded through the lattice. The targets describe the factored
version.

## Files

- `type-naming.md` — names resolve to types through identities and facts (no
  matching `.agent/docs/` file yet)
- `type-world.md` — `Types` is the representation kernel and nothing else
- `set-theoretic-types.md` — a nominal type carries its inner in the symbol
- `protocols.md` — a protocol domain is a marker; impls join the program by demand
