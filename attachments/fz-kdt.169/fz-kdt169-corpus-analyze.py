#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re


OUT = Path("/tmp/fz-kdt169-corpus-20260906")
SIDES = ("retained", "prototype")
PHASES = ("interp", "run", "build", "aot-run")
SUFFIXES = ("rc", "out", "err")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def behavior_bytes(path: Path) -> bytes:
    return re.sub(rb"dyld\[\d+\]", b"dyld[<pid>]", path.read_bytes())


def count_lines(path: Path, prefix: bytes) -> int:
    return sum(line.startswith(prefix) for line in path.read_bytes().splitlines())


def dispatch_counts(path: Path) -> tuple[int, int]:
    lines = path.read_bytes().splitlines()
    plans = sum(line.strip() == b"plan" for line in lines)
    tests = sum(re.match(rb"n\d+ test ", line.strip()) is not None for line in lines)
    return plans, tests


fixtures = [line.strip() for line in (OUT / "fixtures.txt").read_text().splitlines() if line.strip()]
keys = [fixture.removesuffix(".fz").replace("/", "__") for fixture in fixtures]

behavior_movers = []
for fixture, key in zip(fixtures, keys):
    moved = []
    for phase in PHASES:
        for suffix in SUFFIXES:
            left = OUT / "retained" / f"{key}.{phase}.{suffix}"
            right = OUT / "prototype" / f"{key}.{phase}.{suffix}"
            if behavior_bytes(left) != behavior_bytes(right):
                moved.append(f"{phase}.{suffix}")
    if moved:
        behavior_movers.append((fixture, ",".join(moved)))

backend_rows = []
activation_rows = []
for fixture, key in zip(fixtures, keys):
    left_backend = OUT / "retained" / f"{key}.backend"
    right_backend = OUT / "prototype" / f"{key}.backend"
    if left_backend.exists() or right_backend.exists():
        left_counts = (
            (count_lines(left_backend, b"  executable "), *dispatch_counts(left_backend))
            if left_backend.exists()
            else (-1, -1, -1)
        )
        right_counts = (
            (count_lines(right_backend, b"  executable "), *dispatch_counts(right_backend))
            if right_backend.exists()
            else (-1, -1, -1)
        )
        if not left_backend.exists() or not right_backend.exists() or left_backend.read_bytes() != right_backend.read_bytes():
            backend_rows.append((fixture, left_counts, right_counts, digest(left_backend) if left_backend.exists() else "-", digest(right_backend) if right_backend.exists() else "-"))

    left_activations = OUT / "retained" / f"{key}.activations"
    right_activations = OUT / "prototype" / f"{key}.activations"
    if left_activations.exists() or right_activations.exists():
        left_counts = (
            count_lines(left_activations, b"  return:") if left_activations.exists() else -1,
            count_lines(left_activations, b"    @") if left_activations.exists() else -1,
        )
        right_counts = (
            count_lines(right_activations, b"  return:") if right_activations.exists() else -1,
            count_lines(right_activations, b"    @") if right_activations.exists() else -1,
        )
        if not left_activations.exists() or not right_activations.exists() or left_activations.read_bytes() != right_activations.read_bytes():
            activation_rows.append((fixture, left_counts, right_counts, digest(left_activations) if left_activations.exists() else "-", digest(right_activations) if right_activations.exists() else "-"))

claim_rows = []
work_rows = []
claim_totals = {
    side: {"applied": 0, "products": 0, "Activation": [0, 0, 0], "CallSiteSummary": [0, 0, 0], "CallSiteTargets": [0, 0, 0]}
    for side in SIDES
}
for fixture, key in zip(fixtures, keys):
    path = OUT / "claims" / f"{key}.json"
    if not path.exists():
        continue
    record = json.loads(path.read_text())
    for side in SIDES:
        claim_totals[side]["applied"] += record[side]["applied"]
        claim_totals[side]["products"] += record[side]["products"]
        for kind in ("Activation", "CallSiteSummary", "CallSiteTargets"):
            claim_totals[side][kind] = [left + right for left, right in zip(claim_totals[side][kind], record[side][kind])]
    claim_fields = ("Activation", "CallSiteSummary", "CallSiteTargets")
    left_claims = {field: record["retained"][field] for field in claim_fields}
    right_claims = {field: record["prototype"][field] for field in claim_fields}
    if left_claims != right_claims:
        claim_rows.append((fixture, left_claims, right_claims))
    left_work = {field: record["retained"][field] for field in ("applied", "products")}
    right_work = {field: record["prototype"][field] for field in ("applied", "products")}
    if left_work != right_work:
        work_rows.append((fixture, left_work, right_work))

with (OUT / "behavior-movers.tsv").open("w") as handle:
    handle.write("fixture\tcomponents\n")
    for fixture, components in behavior_movers:
        handle.write(f"{fixture}\t{components}\n")

with (OUT / "backend-movers.tsv").open("w") as handle:
    handle.write("fixture\tretained(executables,plans,test_nodes)\tprototype(executables,plans,test_nodes)\tretained_sha256\tprototype_sha256\n")
    for fixture, left, right, left_hash, right_hash in backend_rows:
        handle.write(f"{fixture}\t{left}\t{right}\t{left_hash}\t{right_hash}\n")

with (OUT / "activation-movers.tsv").open("w") as handle:
    handle.write("fixture\tretained(activations,callsites)\tprototype(activations,callsites)\tretained_sha256\tprototype_sha256\n")
    for fixture, left, right, left_hash, right_hash in activation_rows:
        handle.write(f"{fixture}\t{left}\t{right}\t{left_hash}\t{right_hash}\n")

with (OUT / "claim-movers.tsv").open("w") as handle:
    handle.write("fixture\tretained\tprototype\n")
    for fixture, left, right in claim_rows:
        handle.write(f"{fixture}\t{json.dumps(left, sort_keys=True)}\t{json.dumps(right, sort_keys=True)}\n")

with (OUT / "work-movers.tsv").open("w") as handle:
    handle.write("fixture\tretained\tprototype\n")
    for fixture, left, right in work_rows:
        handle.write(f"{fixture}\t{json.dumps(left, sort_keys=True)}\t{json.dumps(right, sort_keys=True)}\n")
(OUT / "claim-totals.json").write_text(json.dumps(claim_totals, indent=2, sort_keys=True) + "\n")

for side in SIDES:
    lines = []
    for fixture, key in zip(fixtures, keys):
        for phase in PHASES:
            for suffix in SUFFIXES:
                path = OUT / side / f"{key}.{phase}.{suffix}"
                lines.append(f"{hashlib.sha256(behavior_bytes(path)).hexdigest()}  {key}.{phase}.{suffix}\n")
    manifest = "".join(sorted(lines))
    manifest_path = OUT / f"{side}-behavior.sha256"
    manifest_path.write_text(manifest)
    (OUT / f"{side}-behavior-manifest.sha256").write_text(f"{hashlib.sha256(manifest.encode()).hexdigest()}  {manifest_path.name}\n")

summary = (
    f"fixtures={len(fixtures)} behavior_files_per_side={len(fixtures) * len(PHASES) * len(SUFFIXES)} "
    f"behavior_movers={len(behavior_movers)} backend_movers={len(backend_rows)} "
    f"activation_movers={len(activation_rows)} claim_movers={len(claim_rows)} "
    f"work_movers={len(work_rows)}\n"
)
(OUT / "summary.txt").write_text(summary)
print(summary, end="")
