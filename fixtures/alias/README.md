---
purpose: "nested-module path aliasing — `alias Long.Path` and `alias Long.Path, as: LP`"
paths: [jit, interp, aot, repl]
---

# alias

Nested-module path aliasing — `alias Long.Path` and `alias Long.Path, as: LP`,
self-checked in-language:

```fz
assert(User.nick_name(40) == 1040, "alias Long.Path then Path.greet")
assert(User.renamed(41) == 1041, "alias Long.Path, as: LP then LP.greet")
```
