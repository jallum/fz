---
purpose: "fz-siu.12 — spawn/2 with min_heap_size hint behaves identically to spawn/1"
paths: [jit, interp, aot]
---

# spawn2_basic

fz-siu.12 — spawn/2 accepts a min_heap_size hint alongside the closure. v1:
hint is accepted and ignored. The spawned task runs identically to spawn/1.
