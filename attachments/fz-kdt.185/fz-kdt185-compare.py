#!/usr/bin/env python3
import argparse
from collections import Counter
import csv
import json
from pathlib import Path
import re


SITE = re.compile(r"  --> runtime:([^:]+):(\d+):")
METRICS = [
    "fz.diag.warning",
    "fz.compiler2.function_contract.defined",
    "fz.compiler2.job.start",
    "fz.compiler2.work_graph.applied",
    "fz.compiler2.activation_analysis.defined",
    "fz.compiler2.pull.product.requested",
    "fz.compiler2.pull.product.evaluated",
    "fz.compiler2.pull.product.settled",
    "fz.compiler2.pull.product.cache_hit",
]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("base")
    parser.add_argument("current")
    parser.add_argument("output_dir")
    args = parser.parse_args()
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    base = {row["fixture"]: row for row in json.loads(Path(args.base).read_text())}
    current = {row["fixture"]: row for row in json.loads(Path(args.current).read_text())}

    def movers(field):
        return [name for name in base if base[name].get(field) != current[name].get(field)]

    def total(metric, side):
        return sum(row.get("stats", {}).get(metric, 0) for row in side.values())

    summary = {
        "sources": len(base),
        "base_backend_producers": sum("backend_sha256" in row for row in base.values()),
        "current_backend_producers": sum("backend_sha256" in row for row in current.values()),
        "rc_movers": len(movers("rc")),
        "stdout_movers": len(movers("stdout_sha256")),
        "diagnostic_movers": len(movers("diagnostics_sha256")),
        "backend_hash_movers": len(movers("backend_sha256")),
        "backend_length_movers": len(movers("backend_bytes")),
        "metrics": {
            metric: {
                "base": total(metric, base),
                "current": total(metric, current),
                "delta": total(metric, current) - total(metric, base),
            }
            for metric in METRICS
        },
    }
    (output / "summary.json").write_text(json.dumps(summary, sort_keys=True, indent=2) + "\n")

    with (output / "diagnostic-movers.tsv").open("w", newline="") as file:
        writer = csv.writer(file, delimiter="\t")
        writer.writerow(["fixture", "base_warnings", "current_warnings", "removed_runtime_sites"])
        for name in movers("diagnostics_sha256"):
            before = base[name]
            after = current[name]
            removed = Counter(SITE.findall(before["diagnostic_text"])) - Counter(
                SITE.findall(after["diagnostic_text"])
            )
            sites = ",".join(
                f"{source}:{line}"
                for (source, line), count in sorted(removed.items())
                for _ in range(count)
            )
            writer.writerow([name, before["stats"].get("fz.diag.warning", 0), after["stats"].get("fz.diag.warning", 0), sites])

    with (output / "backend-movers.tsv").open("w", newline="") as file:
        writer = csv.writer(file, delimiter="\t")
        writer.writerow(["fixture", "base_sha256", "current_sha256", "base_bytes", "current_bytes"])
        for name in movers("backend_sha256"):
            writer.writerow([
                name,
                base[name].get("backend_sha256", ""),
                current[name].get("backend_sha256", ""),
                base[name].get("backend_bytes", ""),
                current[name].get("backend_bytes", ""),
            ])

    with (output / "work-movers.tsv").open("w", newline="") as file:
        writer = csv.writer(file, delimiter="\t")
        writer.writerow(["fixture", "metric", "base", "current", "delta"])
        for metric in METRICS:
            for name in base:
                before = base[name].get("stats", {}).get(metric, 0)
                after = current[name].get("stats", {}).get(metric, 0)
                if before != after:
                    writer.writerow([name, metric, before, after, after - before])


if __name__ == "__main__":
    main()
