#!/usr/bin/env python3
import argparse
import hashlib
import json
import re
from collections import Counter


def behavior_record(row):
    record = {}
    for phase in ("interp", "run", "build", "aot"):
        value = row.get(phase)
        if value is None:
            record[phase] = None
            continue
        stderr = value["stderr"].split("telemetry stats:\n", 1)[0]
        stderr = re.sub(r"thread '([^']+)' \([0-9]+\)", r"thread '\1' (<ID>)", stderr)
        record[phase] = [value["rc"], value["stdout"], stderr, value["timeout"]]
    return record


def main():
    p = argparse.ArgumentParser()
    p.add_argument("base")
    p.add_argument("head")
    p.add_argument("out_prefix")
    args = p.parse_args()
    base = json.load(open(args.base))
    head = json.load(open(args.head))
    b = {r["fixture"]: r for r in base["results"]}
    h = {r["fixture"]: r for r in head["results"]}
    assert b.keys() == h.keys()

    behavior_movers = []
    backend_movers = []
    work_movers = []
    aggregate_base = Counter()
    aggregate_head = Counter()
    duplicate_base = Counter()
    duplicate_head = Counter()
    manifest_base = []
    manifest_head = []
    for fixture in sorted(b):
        br, hr = b[fixture], h[fixture]
        bb, hb = behavior_record(br), behavior_record(hr)
        manifest_base.append([fixture, bb])
        manifest_head.append([fixture, hb])
        if bb != hb:
            behavior_movers.append(fixture)
        bs, hs = br["interp"]["stats"], hr["interp"]["stats"]
        aggregate_base.update(bs)
        aggregate_head.update(hs)
        changed_stats = {k: [bs.get(k, 0), hs.get(k, 0)] for k in sorted(set(bs) | set(hs)) if bs.get(k, 0) != hs.get(k, 0)}
        if changed_stats:
            work_movers.append([fixture, changed_stats])
        bbe, hbe = br.get("backend"), hr.get("backend")
        if bbe:
            duplicate_base.update({"producers": 1, "executables": bbe["executables"], "duplicate_key_extras": bbe["duplicate_key_extras"], "duplicate_key_classes": bbe["duplicate_key_classes"]})
        if hbe:
            duplicate_head.update({"producers": 1, "executables": hbe["executables"], "duplicate_key_extras": hbe["duplicate_key_extras"], "duplicate_key_classes": hbe["duplicate_key_classes"]})
        if bbe != hbe:
            backend_movers.append([fixture, bbe, hbe])

    mb = (json.dumps(manifest_base, sort_keys=True, separators=(",", ":")) + "\n").encode()
    mh = (json.dumps(manifest_head, sort_keys=True, separators=(",", ":")) + "\n").encode()
    summary = {
        "fixture_count": len(b),
        "base_binary": base["binary_sha256"],
        "head_binary": head["binary_sha256"],
        "behavior_manifest_base": hashlib.sha256(mb).hexdigest(),
        "behavior_manifest_head": hashlib.sha256(mh).hexdigest(),
        "behavior_movers": behavior_movers,
        "backend_mover_count": len(backend_movers),
        "work_mover_count": len(work_movers),
        "backend_totals_base": dict(duplicate_base),
        "backend_totals_head": dict(duplicate_head),
        "stats_base": dict(sorted(aggregate_base.items())),
        "stats_head": dict(sorted(aggregate_head.items())),
        "stats_delta": {k: aggregate_head[k] - aggregate_base[k] for k in sorted(set(aggregate_base) | set(aggregate_head)) if aggregate_head[k] != aggregate_base[k]},
    }
    open(args.out_prefix + "-summary.json", "w").write(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    open(args.out_prefix + "-behavior-base.json", "wb").write(mb)
    open(args.out_prefix + "-behavior-head.json", "wb").write(mh)
    with open(args.out_prefix + "-backend-movers.tsv", "w") as f:
        f.write("fixture\tbase_exec\thead_exec\tbase_dup_extras\thead_dup_extras\tbase_sha\thead_sha\n")
        for fixture, x, y in backend_movers:
            f.write(f"{fixture}\t{x and x['executables']}\t{y and y['executables']}\t{x and x['duplicate_key_extras']}\t{y and y['duplicate_key_extras']}\t{x and x['sha256']}\t{y and y['sha256']}\n")
    with open(args.out_prefix + "-work-movers.tsv", "w") as f:
        f.write("fixture\tchanged_stats_json\n")
        for fixture, values in work_movers:
            f.write(f"{fixture}\t{json.dumps(values, sort_keys=True, separators=(',', ':'))}\n")


if __name__ == "__main__":
    main()
