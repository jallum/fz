---
purpose: "fz-ul4.29.5 — spawn-with-captures lift (was forbidden v1)"
paths: [jit, interp]
---

# spawn_with_captures

fz-ul4.29.5 — spawn-with-captures lift (was forbidden v1)

## Notes

Pre-.29.5, fz_spawn asserted captured.len() == 0. With the stub design,
the closure (including captures) is deep-copied into the new task's
heap, then the closure's stub_fp materializes the initial frame.
