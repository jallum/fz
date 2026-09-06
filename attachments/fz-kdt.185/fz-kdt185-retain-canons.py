#!/usr/bin/env python3
import argparse
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("base_binary")
    parser.add_argument("current_binary")
    parser.add_argument("base_results")
    parser.add_argument("current_results")
    parser.add_argument("root")
    parser.add_argument("output_dir")
    args = parser.parse_args()
    base_rows = {row["fixture"]: row for row in json.loads(Path(args.base_results).read_text())}
    current_rows = {row["fixture"]: row for row in json.loads(Path(args.current_results).read_text())}
    root = Path(args.root).resolve()
    output_root = Path(args.output_dir)
    for name, before in base_rows.items():
        if before.get("backend_sha256") == current_rows[name].get("backend_sha256"):
            continue
        for side, binary in (("base", args.base_binary), ("current", args.current_binary)):
            output = output_root / side / f"{Path(name).stem}.backend"
            output.parent.mkdir(parents=True, exist_ok=True)
            command = [binary, "interp", "--dump", f"backend={output}", name]
            subprocess.run(command, cwd=root, capture_output=True, check=True)


if __name__ == "__main__":
    main()
