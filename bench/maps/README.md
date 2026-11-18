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
| `replace_12` | six puts of present keys into a 12-key map |
| `delete_12` | three deletes, then three puts of the same keys |

`_a_` probes use atom keys and `_b_` probes use binary keys. A 40-key map is past the flat
limit of 32 entries, so those probes run on the trie and have no floor.

The Erlang twins call `Mod:put`, `Mod:get` and `Mod:remove` with `Mod` read from the environment
at run time. With the module visible, the Erlang compiler folds a chain of puts with literal keys
into one instruction, which is a different workload.

## The floor

`floor/flat.s` holds the sequences and `floor/harness.c` checks them against a reference model
over random puts and deletes of atom, integer and binary keys, then runs the probes on them.
Its loop is C, with no collector and no call from compiled code, so it bounds a runtime path from
below; it does not predict it.

- `fz_flat_scan` finds a one-word key by word equality.
- `fz_flat_place` finds the slot for an absent one-word key by term order.
- `fz_flat_find` does both in one ordered search (the `ordered` column, puts and gets only).
- `fz_flat_find_bin` finds a binary key, or its slot, by bytes then length.
- `fz_flat_write` writes the new map with an entry inserted, replaced or left out.

An atom's order is read from a table of name prefixes: the first eight bytes of its name as a
big-endian word. Two atoms that share a prefix leave the fast path.

## Recorded figures

Bench host (Apple M5 Pro), OTP 28 with the JIT, fz at the commit that last changed this table.

| Probe | fz | BEAM | floor | ordered |
|---|---:|---:|---:|---:|
| build_a_6 | 4,341 | 2,681 | 1,133 | 988 |
| build_b_6 | 5,268 | 6,420 | 1,176 | |
| build_a_12 | 9,369 | 6,791 | 2,914 | 2,424 |
| build_b_12 | 11,353 | 19,917 | 3,050 | |
| build_a_24 | 20,140 | 18,072 | 8,139 | 6,331 |
| build_b_24 | 24,391 | 88,218 | 8,057 | |
| build_a_40 | 71,370 | 48,401 | | |
| build_b_40 | 94,448 | 193,483 | | |
| get_a_12 | 6,127 | 1,555 | 497 | 540 |
| get_b_12 | 12,790 | 6,694 | 900 | |
| get_a_40 | 8,312 | 1,635 | | |
| get_b_40 | 15,234 | 4,017 | | |
| replace_a_12 | 4,706 | 2,903 | 1,506 | 1,590 |
| replace_b_12 | 5,673 | 7,926 | 1,847 | |
| delete_a_12 | 14,718 | 3,796 | 1,657 | 1,460 |
| delete_b_12 | 22,333 | 13,720 | 2,035 | |
