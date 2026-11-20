# Map probes

Small map workloads run three ways: compiled by fz, on BEAM, and on hand-written arm64
sequences that work directly on the flat map layout. The hand-written column is the floor a
runtime path is measured against.

```
python3 bench/maps/probes.py build --fz2 target/release/fz2 --out /some/dir
python3 bench/maps/probes.py measure --out /some/dir
```

`build` needs the fz release binary and a C compiler. `measure` needs `python3` and
`/usr/bin/time -l` (macOS); the BEAM column needs `erlc` and `erl` on the path and is left out
without them. The directory `build` fills can be copied to another host and measured there.

## What a figure is

Instructions retired per iteration, taken as a slope between a run of N iterations and a run of
2N, so process start-up cancels. Every run's printed answer is checked against the expected one.

| Probe | One iteration |
|---|---|
| `build_K` | an empty map, then K puts of new keys |
| `get_K` | six `Map.get/3` calls for present keys of a K-key map |
| `case_K` | six calls of a function that matches `%{^key => value}` on a K-key map and adds what it finds |
| `replace_12` | six puts of present keys into a 12-key map |
| `delete_12` | three deletes, then three puts of the same keys |

`_a_` probes use atom keys and `_b_` probes use binary keys. A 40-key map is past the flat
limit of 32 entries, so those probes run on the trie; `get_a_40` and `case_a_40` have the trie
walk as their floor, and the binary-key and build probes on 40 keys have none.

The `case` twin matches `#{K := V}` in a function of its own. The other Erlang twins call
`Mod:put`, `Mod:get` and `Mod:remove` with `Mod` read from the environment
at run time. With the module visible, the Erlang compiler folds a chain of puts with literal keys
into one instruction, which is a different workload.

## The floor

`floor/flat.s` and `floor/trie.s` hold the sequences, and `floor/harness.c` checks them against a
reference model: the flat ones over random puts and deletes of atom, integer and binary keys, the
trie walk over random tries of 2 to 301 atom and integer keys, some sharing a hash. It builds a
trie by the runtime's rule from the runtime's hashes, so the probe keys take the shape fz gives
them, then runs the probes.
Its loop is C, with no collector and no call from compiled code, so it bounds a runtime path from
below; it does not predict it.

- `fz_flat_scan` finds a one-word key by word equality.
- `fz_flat_get` is that scan with the value read where the key was found. It is the sequence the
  compiler emits for a map pattern whose key is an atom or an integer (`WordKeyFind` in
  `src/compiler2/native_codegen/clif.rs`), and the floor of the `case` probes.
- `fz_flat_place` finds the slot for an absent one-word key by term order.
- `fz_flat_find` does both in one ordered search (the `ordered` column, puts and gets only).
- `fz_flat_find_bin` finds a binary key, or its slot, by bytes then length.
- `fz_flat_write` writes the new map with an entry inserted, replaced or left out.

- `fz_trie_get` finds a one-word key in a trie by its hash, with a popcount at each node, and
  `fz_trie_get_atom` reads an atom's key hash through the process first. They are the sequence
  the compiler emits for such a pattern on a trie, and the floor of `get_a_40` and `case_a_40`.

An atom's order is read from a table of name prefixes: the first eight bytes of its name as a
big-endian word. Two atoms that share a prefix leave the fast path.

## Recorded figures

Bench host (Apple M5 Pro), OTP 28.3 with the JIT, fz at the commit that last changed this table.

| Probe | fz | BEAM | floor | ordered |
|---|---:|---:|---:|---:|
| build_a_6 | 3,989 | 2,624 | 1,133 | 988 |
| build_b_6 | 5,254 | 6,421 | 1,176 |  |
| build_a_12 | 8,812 | 6,856 | 2,914 | 2,424 |
| build_b_12 | 11,477 | 19,887 | 3,049 |  |
| build_a_24 | 19,138 | 18,148 | 8,139 | 6,330 |
| build_b_24 | 24,748 | 88,196 | 8,057 |  |
| build_a_40 | 67,995 | 46,969 |  |  |
| build_b_40 | 100,135 | 190,627 |  |  |
| get_a_12 | 2,633 | 1,554 | 522 | 563 |
| get_b_12 | 5,214 | 6,696 | 924 |  |
| get_a_40 | 2,574 | 1,653 | 384 |  |
| get_b_40 | 6,593 | 4,033 |  |  |
| case_a_12 | 2,633 | 511 | 455 | 472 |
| case_b_12 | 5,214 | 5,538 | 949 |  |
| case_a_40 | 2,574 | 606 | 384 |  |
| case_b_40 | 6,593 | 2,874 |  |  |
| replace_a_12 | 3,393 | 2,970 | 1,531 | 1,615 |
| replace_b_12 | 4,713 | 7,980 | 1,873 |  |
| delete_a_12 | 4,024 | 3,843 | 1,682 | 1,484 |
| delete_b_12 | 5,522 | 13,794 | 2,062 |  |