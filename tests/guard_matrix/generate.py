#!/usr/bin/env python3
"""Writes programs.json: the mixed-lane guard programs and Elixir's answer to each.

    python3 tests/guard_matrix/generate.py tests/guard_matrix/programs.json

Needs `elixir` on PATH. Every operator in {+ - * / div rem, unary minus} is
paired with every operand kind: an integer, a float, `integer | float`, and an
untyped value. The right operand is also an integer or a float literal. Each
shape is written twice, as an entry guard on a function head and as a receive
guard (where the kinds come from `is_integer`, `is_float`, their `or`, and no
test at all). A program evaluates every pair of values its operand kinds allow
and prints the list of answers `:a` (the guard held) and `:b` (it did not).
Elixir's list is the expected output; a program Elixir cannot run stops the
generator.
"""
import json
import re
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ANNOTATION = {"int": "integer", "float": "float", "union": "integer | float", "any": None}
VALUES = {"int": ["7"], "float": ["7.0"], "union": ["7", "7.0"], "any": ["7", "7.0"]}
LITERAL = {"lit_int": "2", "lit_float": "2.0"}
OPERATORS = ["+", "-", "*", "/", "div", "rem", "neg"]
OPERATOR_NAME = {"+": "add", "-": "sub", "*": "mul", "/": "fdiv"}


def comparison(op, a, b):
    if op == "neg":
        return f"-{a} < 0"
    if op in ("div", "rem"):
        return f"{op}({a}, {b}) >= 0"
    return f"{a} {op} {b} >= 0"


def kind_test(kind, var):
    return {
        "int": f"is_integer({var})",
        "float": f"is_float({var})",
        "union": f"(is_integer({var}) or is_float({var}))",
        "any": None,
    }[kind]


def annotated(kind, var):
    return var if ANNOTATION[kind] is None else f"{var} :: {ANNOTATION[kind]}"


def conjunction(*parts):
    return " and ".join(part for part in parts if part)


def value_pairs(left_kind, right_kind):
    right_values = {"lit_int": ["2"], "lit_float": ["2.0"], "-": [None]}.get(right_kind) or VALUES[right_kind]
    return [(left, right) for left in VALUES[left_kind] for right in right_values]


def entry_program(op, left_kind, right_kind):
    pairs = value_pairs(left_kind, right_kind)
    if op == "neg" or right_kind in LITERAL:
        right = LITERAL.get(right_kind)
        head = f"def f({annotated(left_kind, 'a')}) when {comparison(op, 'a', right)}, do: :a\ndef f(_), do: :b\n"
        calls = ", ".join(f"f({l})" for l, _ in pairs)
    else:
        head = (
            f"def f({annotated(left_kind, 'a')}, {annotated(right_kind, 'b')}) "
            f"when {comparison(op, 'a', 'b')}, do: :a\ndef f(_, _), do: :b\n"
        )
        calls = ", ".join(f"f({l}, {r})" for l, r in pairs)
    return head + f"def main() do\n  dbg([{calls}])\nend\n"


def receive_program(op, left_kind, right_kind):
    pairs = value_pairs(left_kind, right_kind)
    if op == "neg" or right_kind in LITERAL:
        right = LITERAL.get(right_kind)
        guard = conjunction(kind_test(left_kind, "a"), comparison(op, "a", right))
        pattern = "a"
        calls = ", ".join(f"g({l})" for l, _ in pairs)
    else:
        guard = conjunction(kind_test(left_kind, "a"), kind_test(right_kind, "b"), comparison(op, "a", "b"))
        pattern = "{a, b}"
        calls = ", ".join(f"g({{{l}, {r}}})" for l, r in pairs)
    head = (
        f"def g(m) do\n  send(self(), m)\n  receive do\n    {pattern} when {guard} -> :a\n    _ -> :b\n  end\nend\n"
    )
    return head + f"def main() do\n  dbg([{calls}])\nend\n"


def programs():
    for op in OPERATORS:
        for left_kind in ["int", "float", "union", "any"]:
            right_kinds = ["-"] if op == "neg" else ["lit_int", "lit_float", "int", "float", "union", "any"]
            for right_kind in right_kinds:
                stem = f"{OPERATOR_NAME.get(op, op)}_{left_kind}_{right_kind}"
                yield stem + "_entry", entry_program(op, left_kind, right_kind)
                yield stem + "_recv", receive_program(op, left_kind, right_kind)


def elixir_twin(source):
    """The same functions in a module, without the fz type annotations."""
    functions, main = source.split("def main() do\n  dbg(")
    answers = main.rsplit(")\nend", 1)[0].strip()
    functions = re.sub(r" :: [a-z]+( \| [a-z]+)?", "", functions)
    body = "".join("  " + line + "\n" for line in functions.strip().split("\n"))
    return f"defmodule M do\n{body}  def main(), do: IO.inspect({answers}, charlists: :as_lists)\nend\nM.main()\n"


def elixir_answer(item):
    name, source = item
    with tempfile.TemporaryDirectory() as directory:
        script = Path(directory) / "program.exs"
        script.write_text(elixir_twin(source))
        result = subprocess.run(["elixir", str(script)], capture_output=True, text=True, timeout=120)
    if result.returncode != 0:
        sys.exit(f"elixir failed on {name}:\n{result.stderr}")
    return {"name": name, "source": source, "expected": result.stdout.strip()}


def main():
    destination = Path(sys.argv[1])
    with ThreadPoolExecutor(6) as pool:
        table = list(pool.map(elixir_answer, programs()))
    destination.write_text(json.dumps(table, indent=1) + "\n")
    print(f"wrote {len(table)} programs to {destination}")


main()
