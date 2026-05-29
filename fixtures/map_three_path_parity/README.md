---
purpose: "map layout three-path parity for lookup, update, floats, nil miss, and pointer values"
paths: [jit, interp, aot, repl]
---

# map_three_path_parity

Map layout three-path parity for lookup, update, float values, nil miss, and
pointer values. Self-checked in-language:

```fz
m = %{b: 2, a: 1, pi: 1.5, xs: xs}
n = %{m | b: 20, c: 3}
assert(n[:b] == 20, "map update overrides an existing key")
assert(n[:missing] == nil, "missing key lookup yields nil")
assert(n[:xs] == [1, 2], "pointer value lookup returns the bound list")
```
