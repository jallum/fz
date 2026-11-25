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
| `to_list_i_K` | `Map.to_list/1` of a K-key map, and the length of the result |
| `keys_i_K` | `Map.keys/1` of a K-key map, and the length of the result |
| `reduce_i_K` | `Enum.reduce/3` over a K-key map, summing its values |
| `next_i_K` | `:maps.next/1` down a K-key map's iterator, summing its values |
| `fold_i_K` | `:maps.fold/3` over a K-key map, summing its values |

`_a_` probes use atom keys and `_b_` probes use binary keys. A 40-key map is past the flat
limit of 32 entries, so those probes run on the trie; `get_a_40` and `case_a_40` have the trie
walk as their floor, and the binary-key and build probes on 40 keys have none.

The walk probes (`_i_`, integer keys) run on 40 and 100,000 keys, and their figures are per
entry: the slope divided by K. `reduce`, `next` and `fold` have no floor.

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

- `fz_map_keys`, `fz_map_values` and `fz_map_pairs` (`floor/walk.s`) turn a flat map or a trie
  into the list of its keys, its values or its `{key, value}` pairs in one pass, placing each cell
  and linking it to the one before, so the list is built front to back and never reversed. They
  are the floor of the walk probes.
- `fz_map_next_batch` (`floor/walk.s`) places one batch of an iterator's walk: from entry `index`,
  up to 32 `{key, value, next}` tuples, each linked to the one after it, the last linked to the
  continuation `[index + 32 | map]` or to `none`. It reaches the start by skipping whole trie
  children by their totals, then places each entry in one step. The harness checks the batch from
  every start of every map it builds, and that a bump with a byte too few places nothing. It has
  no probe row: `next_i_K` and `fold_i_K` run the language's own walk.

- `fz_trie_get` finds a one-word key in a trie by its hash, with a popcount at each node, and
  `fz_trie_get_atom` reads an atom's key hash through the process first. They are the sequence
  the compiler emits for such a pattern on a trie, and the floor of `get_a_40` and `case_a_40`.

An atom's order is read from a table of name prefixes: the first eight bytes of its name as a
big-endian word. Two atoms that share a prefix leave the fast path.

## Recorded figures

Bench host (Apple M5 Pro), OTP 28.3 with the JIT, fz at the commit that last changed this table.

| Probe | fz | BEAM | floor | ordered |
|---|---:|---:|---:|---:|
| build_a_6 | 3,989 | 2,651 | 1,134 | 989 |
| build_b_6 | 5,255 | 6,430 | 1,177 |  |
| build_a_12 | 8,812 | 6,752 | 2,915 | 2,425 |
| build_b_12 | 11,476 | 20,062 | 3,051 |  |
| build_a_24 | 19,141 | 18,256 | 8,140 | 6,332 |
| build_b_24 | 24,746 | 88,290 | 8,058 |  |
| build_a_40 | 67,807 | 45,521 |  |  |
| build_b_40 | 100,073 | 193,719 |  |  |
| get_a_12 | 2,525 | 1,555 | 522 | 565 |
| get_b_12 | 5,106 | 6,701 | 925 |  |
| get_a_40 | 2,465 | 1,623 | 383 |  |
| get_b_40 | 6,485 | 4,031 |  |  |
| case_a_12 | 2,525 | 490 | 455 | 456 |
| case_b_12 | 5,106 | 5,548 | 950 |  |
| case_a_40 | 2,466 | 587 | 383 |  |
| case_b_40 | 6,484 | 2,875 |  |  |
| replace_a_12 | 3,393 | 2,891 | 1,532 | 1,616 |
| replace_b_12 | 4,713 | 7,909 | 1,874 |  |
| delete_a_12 | 4,023 | 3,907 | 1,683 | 1,486 |
| delete_b_12 | 5,522 | 13,787 | 2,063 |  |

| Walk | fz | BEAM | floor |
|---|---:|---:|---:|
| to_list_i_40 | 101 | 112 | 31 |
| keys_i_40 | 71 | 113 | 26 |
| reduce_i_40 | 893 | 156 |  |
| to_list_i_100000 | 116 | 154 | 33 |
| keys_i_100000 | 78 | 97 | 27 |
| reduce_i_100000 | 1,549 | 198 |  |
| next_i_40 | pending bench | pending bench |  |
| fold_i_40 | pending bench | pending bench |  |
| next_i_100000 | pending bench | pending bench |  |
| fold_i_100000 | pending bench | pending bench |  |
