#!/usr/bin/env python3
import argparse
import json
from pathlib import Path
import re


ENUM_LAMBDA = re.compile(r"((?:Enum|Enumerable)\.[A-Za-z0-9_?!]+/\d+#lambda)@\d+-\d+")
ENUM_SPAN = re.compile(r"(@runtime:Enum\.fz:)\d+-\d+")


def normalized(text):
    for pattern in (ENUM_LAMBDA, ENUM_SPAN):
        text = pattern.sub(r"\1<source-range>", text)
    return text


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("base_dir")
    parser.add_argument("current_dir")
    parser.add_argument("output")
    args = parser.parse_args()
    base_dir = Path(args.base_dir)
    current_dir = Path(args.current_dir)
    compared = 0
    movers = []
    for base_path in sorted(base_dir.glob("*.backend")):
        compared += 1
        current_path = current_dir / base_path.name
        if normalized(base_path.read_text()) != normalized(current_path.read_text()):
            movers.append(base_path.name)
    Path(args.output).write_text(json.dumps({"compared": compared, "semantic_movers": movers}, sort_keys=True, indent=2) + "\n")


if __name__ == "__main__":
    main()
