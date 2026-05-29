---
purpose: "&name/arity parses as an explicit function reference, disambiguating overloaded names by arity"
paths: [jit, interp, aot, repl]
---

# fn_ref_ampersand

`&name/arity` parses as an explicit function reference, disambiguating overloaded
names by arity. These are top-level fns (no module), so the claim is purely
behavioural and self-checked in-language:

```fz
assert(apply1(&double/1, 21) == 42, "&double/1 reference applied")
assert(apply2(&add/2, 30, 12) == 42, "&add/2 disambiguated by arity")
```
