#!/usr/bin/env bash
# Campaign scaffolding (fz-kdt.94; removal ticket: fz-kdt.95).
#
# Compares HEAD's canonical backend dumps against the merge-base with a
# base ref, rebuilding the base from source in a temporary worktree: the
# base branch is the golden, reconstructed on demand -- no stored dumps.
# Exit 0 = byte-neutral artifact. Non-zero = movement; per-fixture unified
# diffs are written next to the dumps for the landing's evidence.
#
# Usage: tools/canon-gate.sh [base-ref]   (default: origin/main)
set -euo pipefail

BASE_REF="${1:-origin/main}"
FIXTURES=(
  fixtures2/00420_enum_take_drop_split.fz
  fixtures2/behavior/fz_f98_range_map_converges.fz
  fixtures2/behavior/enum_predicate_search.fz
)

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"
BASE="$(git merge-base HEAD "$BASE_REF")"
OUT="${CANON_GATE_DIR:-$(mktemp -d -t canon-gate)}"
BASE_WT="$OUT/base-worktree"

echo "canon-gate: HEAD=$(git rev-parse --short HEAD) vs base=$(git rev-parse --short "$BASE") (merge-base with $BASE_REF)"
git worktree add --detach "$BASE_WT" "$BASE" >/dev/null 2>&1
trap 'git worktree remove --force "$BASE_WT" >/dev/null 2>&1 || true' EXIT

cargo build --quiet --bin fz2
(cd "$BASE_WT" && cargo build --quiet --bin fz2)

status=0
for fx in "${FIXTURES[@]}"; do
  name="$(basename "$fx" .fz)"
  ./target/debug/fz2 interp --dump "backend=$OUT/$name.head.canon" "$fx" >/dev/null
  (cd "$BASE_WT" && ./target/debug/fz2 interp --dump "backend=$OUT/$name.base.canon" "$fx" >/dev/null)
  if cmp -s "$OUT/$name.base.canon" "$OUT/$name.head.canon"; then
    echo "  $name: byte-identical"
  else
    status=1
    diff -u "$OUT/$name.base.canon" "$OUT/$name.head.canon" > "$OUT/$name.diff" || true
    lines="$(grep -c '^[+-][^+-]' "$OUT/$name.diff" || true)"
    echo "  $name: MOVED ($lines changed lines) -- report: $OUT/$name.diff"
  fi
done
exit $status
