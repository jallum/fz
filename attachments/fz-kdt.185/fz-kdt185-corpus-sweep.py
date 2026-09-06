#!/usr/bin/env python3
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


STATS = re.compile(r"^  (fz\.[^ ]+)\s+(\d+)$", re.MULTILINE)
DIAG = re.compile(r"^(warning|error)\[([^]]+)\]:", re.MULTILINE)
ADDRESS = re.compile(r"0x[0-9a-fA-F]+")
THREAD = re.compile(r"\(\d+\)")


def normalized(text):
    return THREAD.sub("(<thread>)", ADDRESS.sub("0x<address>", text))


def run_one(binary, fixture, root):
    with tempfile.TemporaryDirectory(prefix="fz-kdt185-sweep-") as tmp:
        tmp = Path(tmp)
        telemetry = tmp / "telemetry.jsonl"
        backend = tmp / "backend.txt"
        command = [
            binary,
            "--emit=stats",
            "--log-telemetry",
            str(telemetry),
            "interp",
            "--dump",
            f"backend={backend}",
            str(fixture),
        ]
        try:
            ran = subprocess.run(command, cwd=root, capture_output=True, timeout=180)
        except subprocess.TimeoutExpired:
            return {"fixture": str(fixture.relative_to(root)), "timeout": True}
        stdout = ran.stdout.decode("utf-8", "replace")
        stderr = ran.stderr.decode("utf-8", "replace")
        stats = {name: int(count) for name, count in STATS.findall(stderr)}
        diagnostic_text = stderr.split("telemetry stats:\n", 1)[0]
        result = {
            "fixture": str(fixture.relative_to(root)),
            "rc": ran.returncode,
            "stdout_sha256": hashlib.sha256(normalized(stdout).encode()).hexdigest(),
            "diagnostics_sha256": hashlib.sha256(normalized(diagnostic_text).encode()).hexdigest(),
            "diagnostics": DIAG.findall(diagnostic_text),
            "diagnostic_text": diagnostic_text,
            "stats": stats,
        }
        if backend.exists():
            content = backend.read_bytes()
            result["backend_sha256"] = hashlib.sha256(content).hexdigest()
            result["backend_bytes"] = len(content)
        return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("binary")
    parser.add_argument("output")
    parser.add_argument("--root", default=".")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    root = Path(args.root).resolve()
    fixtures = sorted(root.glob("fixtures2/**/*.fz"))
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        results = list(pool.map(lambda fixture: run_one(args.binary, fixture, root), fixtures))
    Path(args.output).write_text(json.dumps(results, sort_keys=True, indent=2) + "\n")
    producers = sum("backend_sha256" in result for result in results)
    print(json.dumps({"fixtures": len(fixtures), "backend_producers": producers}, sort_keys=True))


if __name__ == "__main__":
    main()
