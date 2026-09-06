#!/usr/bin/env python3
import argparse
import concurrent.futures
import collections
import hashlib
import json
import os
import pathlib
import re
import subprocess
import tempfile


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def normalized(data: bytes, binary: pathlib.Path, temp: pathlib.Path) -> str:
    text = data.decode("utf-8", "replace")
    for value in (str(binary), str(temp)):
        text = text.replace(value, "<PATH>")
    text = re.sub(r"0x[0-9a-fA-F]+", "0x<ADDR>", text)
    text = re.sub(r"#(?:PID|Thread)<[0-9.]+>", "#<RUNTIME-ID>", text)
    text = re.sub(r"\bthread(?:_id)?[=: ]+[0-9]+\b", "thread=<ID>", text, flags=re.I)
    text = re.sub(r"\bdyld\[[0-9]+\]", "dyld[<PID>]", text)
    return text


def run(command, cwd, timeout=30):
    try:
        p = subprocess.run(command, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
        return p.returncode, p.stdout, p.stderr, False
    except subprocess.TimeoutExpired as e:
        return 124, e.stdout or b"", e.stderr or b"", True


def stats(stderr: str):
    result = {}
    marker = "telemetry stats:\n"
    if marker not in stderr:
        return result
    for line in stderr.split(marker, 1)[1].splitlines():
        match = re.match(r"\s{2}(\S+)\s+(\d+)\s*$", line)
        if match:
            result[match.group(1)] = int(match.group(2))
    return result


def backend_facts(data: bytes):
    text = data.decode("utf-8", "replace")
    keys = [line[8:] for line in text.splitlines() if line.startswith("    key ")]
    counts = collections.Counter(keys)
    extras = sum(count - 1 for count in counts.values())
    return {
        "sha256": sha(data),
        "bytes": len(data),
        "executables": sum(line.startswith("  executable ") for line in text.splitlines()),
        "duplicate_key_extras": extras,
        "duplicate_key_classes": sum(count > 1 for count in counts.values()),
    }


def one(binary: pathlib.Path, root: pathlib.Path, fixture: pathlib.Path):
    rel = fixture.relative_to(root).as_posix()
    with tempfile.TemporaryDirectory(prefix="kdt182-") as td:
        temp = pathlib.Path(td)
        trace = temp / "trace.jsonl"
        backend = temp / "backend.txt"
        interp = run(
            [str(binary), "--emit=stats", "--log-telemetry", str(trace), "interp", "--dump", f"backend={backend}", rel],
            root,
        )
        interp_err = normalized(interp[2], binary, temp)
        result = {
            "fixture": rel,
            "interp": {
                "rc": interp[0], "stdout": normalized(interp[1], binary, temp),
                "stderr": interp_err, "timeout": interp[3], "stats": stats(interp_err),
            },
        }
        if backend.exists():
            result["backend"] = backend_facts(backend.read_bytes())

        run_phase = run([str(binary), "run", rel], root)
        result["run"] = {
            "rc": run_phase[0], "stdout": normalized(run_phase[1], binary, temp),
            "stderr": normalized(run_phase[2], binary, temp), "timeout": run_phase[3],
        }

        aot = temp / "program"
        build = run([str(binary), "build", rel, "-o", str(aot)], root, timeout=60)
        result["build"] = {
            "rc": build[0], "stdout": normalized(build[1], binary, temp),
            "stderr": normalized(build[2], binary, temp), "timeout": build[3],
        }
        if build[0] == 0 and aot.exists():
            execute = run([str(aot)], root)
            result["aot"] = {
                "rc": execute[0], "stdout": normalized(execute[1], binary, temp),
                "stderr": normalized(execute[2], binary, temp), "timeout": execute[3],
            }
        return result


def main():
    p = argparse.ArgumentParser()
    p.add_argument("binary", type=pathlib.Path)
    p.add_argument("output", type=pathlib.Path)
    p.add_argument("--root", type=pathlib.Path, required=True)
    p.add_argument("--workers", type=int, default=4)
    args = p.parse_args()
    root = args.root.resolve()
    binary = args.binary.resolve()
    fixtures = sorted((root / "fixtures2").rglob("*.fz"))
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        results = list(pool.map(lambda fixture: one(binary, root, fixture), fixtures))
    payload = {"binary_sha256": sha(binary.read_bytes()), "fixture_count": len(fixtures), "results": results}
    args.output.write_text(json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
