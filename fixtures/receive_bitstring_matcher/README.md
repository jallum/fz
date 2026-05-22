---
purpose: "receive matcher supports bitstring patterns without AST fallback"
paths: [jit, interp, aot]
---

# receive_bitstring_matcher

fz-puj.50 — bitstring receive clauses lower to first-class Matcher
bitstring tests. The matcher extracts fields while probing the mailbox,
then routes to the matching clause without using the receive AST pattern
walker.
