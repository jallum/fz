#!/usr/bin/env python3
from __future__ import annotations

import concurrent.futures
from collections import defaultdict
import json
import os
from pathlib import Path
import signal
import subprocess
import threading


ROOT = Path("/Users/j5n/Workspace/fz")
OUT = Path("/tmp/fz-kdt169-corpus-20260906")
SIDES = {
    "retained": Path("/tmp/fz-kdt169-base-fz2"),
    "prototype": Path("/tmp/fz-kdt169-full-prototype-fz2"),
}
TIMEOUT_SECONDS = 30
KINDS = ("Activation", "CallSiteSummary", "CallSiteTargets")
print_lock = threading.Lock()


def fixture_key(path: Path) -> str:
    return "__".join(path.relative_to(ROOT).parts).removesuffix(".fz")


def lifecycle(trace: Path) -> dict:
    identities = {kind: set() for kind in KINDS}
    first = defaultdict(int)
    retractions = defaultdict(int)
    events = defaultdict(int)
    with trace.open() as handle:
        for line in handle:
            event = json.loads(line)
            name = ".".join(event.get("name", []))
            events[name] += 1
            metadata = event.get("metadata", {})
            owner = metadata.get("completion") or metadata.get("step") or {}
            for change in owner.get("changed", []):
                kind = change.get("kind")
                if kind not in identities:
                    continue
                identity = tuple(
                    sorted(
                        (key, json.dumps(value, sort_keys=True, separators=(",", ":")))
                        for key, value in change.items()
                        if key not in {"old_revision", "new_revision", "old_settled", "new_settled"}
                    )
                )
                identities[kind].add(identity)
                if change.get("old_revision") is None and change.get("new_revision") is not None:
                    first[kind] += 1
                if change.get("old_revision") is not None and change.get("new_revision") is None:
                    retractions[kind] += 1
    return {
        "Activation": [len(identities["Activation"]), first["Activation"], retractions["Activation"]],
        "CallSiteSummary": [
            len(identities["CallSiteSummary"]),
            first["CallSiteSummary"],
            retractions["CallSiteSummary"],
        ],
        "CallSiteTargets": [
            len(identities["CallSiteTargets"]),
            first["CallSiteTargets"],
            retractions["CallSiteTargets"],
        ],
        "jobs": events["fz.compiler2.job.start"],
        "applied": events["fz.compiler2.work_graph.applied"],
        "products": events["fz.compiler2.pull.product.evaluated"],
        "activation_analysis": events["fz.compiler2.activation_analysis.defined"],
        "callsite_defined": events["fz.compiler2.callsite.defined"],
    }


def run_one(side: str, fixture: Path) -> dict:
    key = fixture_key(fixture)
    trace = OUT / f"{side}-{key}.trace.jsonl"
    process = subprocess.Popen(
        [str(SIDES[side]), "--log-telemetry", str(trace), "interp", str(fixture)],
        cwd=ROOT,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )
    try:
        rc = process.wait(timeout=TIMEOUT_SECONDS)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.wait()
        rc = 124
    result = lifecycle(trace) if trace.exists() else {}
    result["rc"] = rc
    trace.unlink(missing_ok=True)
    return result


def run_fixture(index_fixture: tuple[int, Path]) -> None:
    index, fixture = index_fixture
    key = fixture_key(fixture)
    record = {side: run_one(side, fixture) for side in SIDES}
    (OUT / "claims" / f"{key}.json").write_text(json.dumps(record, sort_keys=True) + "\n")
    if index % 20 == 0:
        with print_lock:
            print(f"claims {index}/{len(FIXTURES)} {fixture.relative_to(ROOT)}", flush=True)


all_fixtures = [ROOT / line.strip() for line in (OUT / "fixtures.txt").read_text().splitlines() if line.strip()]
FIXTURES = [fixture for fixture in all_fixtures if (OUT / "retained" / f"{fixture_key(fixture)}.backend").exists()]
(OUT / "claims").mkdir(exist_ok=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
    list(executor.map(run_fixture, enumerate(FIXTURES, start=1)))
print(f"claim sweep complete: {len(FIXTURES)} backend-producing fixtures", flush=True)
