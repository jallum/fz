---
purpose: "&name/arity parses as an explicit function reference, disambiguating overloaded names by arity"
paths: [jit, interp]
---

# fn_ref_ampersand

fz-swt.5 — Elixir-style `&name/arity` syntax for first-class function
references. Today a bare name lowered to a zero-capture closure picks
"first defined wins" for overloaded names; `&pick/1` vs `&pick/2` makes
that choice explicit.
