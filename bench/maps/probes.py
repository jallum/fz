#!/usr/bin/env python3
"""Map probes: the same small workload on fz, on BEAM, and on the hand-written sequences.

  probes.py build --fz2 target/release/fz2 --out DIR    write sources, build fz binaries and the floor
  probes.py measure --out DIR                           run everything in DIR, print instructions per iteration

A figure is a slope: (instructions at 2N iterations - instructions at N) / N, so start-up cancels.
A walk row (`to_list`, `keys`, `reduce`) turns a map of integer keys into a list once per iteration,
and its figure is per entry: the slope divided by the map's size.
`measure` needs only python3, /usr/bin/time and, for the BEAM column, erlc and erl; DIR can be
built on one host and measured on another.
"""
import argparse, os, shutil, subprocess, sys

KEYS = ["id", "name", "kind", "value", "flags", "owner", "alpha", "bravo", "charlie", "delta", "echo",
        "foxtrot", "golf", "hotel", "india", "juliet", "kilo", "lima", "mike", "november", "oscar", "papa",
        "quebec", "romeo", "sierra", "tango", "uniform", "victor", "whiskey", "xray", "yankee", "zulu",
        "north", "south", "east", "west", "red", "green", "blue", "amber"]
PICKS = [0, 5, 11, 8, 3, 9]
FLAT_MAX = 32

# (operation, keys in the map, fz iterations, BEAM iterations); the second run of each doubles them.
SHAPES = [("build", 6, 200_000, 2_000_000), ("build", 12, 200_000, 1_000_000), ("build", 24, 100_000, 500_000),
          ("build", 40, 50_000, 250_000), ("get", 12, 500_000, 2_000_000), ("get", 40, 500_000, 2_000_000),
          ("case", 12, 500_000, 2_000_000), ("case", 40, 500_000, 2_000_000),
          ("replace", 12, 500_000, 2_000_000), ("delete", 12, 500_000, 2_000_000)]
PROBES = [(op, kind, k, fz_n, beam_n) for (op, k, fz_n, beam_n) in SHAPES for kind in "ab"]
# (walk, keys in the map, fz iterations, BEAM iterations); the map's keys are (j + 1) * 7919 with value j.
WALK_SHAPES = [("to_list", 40, 50_000, 200_000), ("keys", 40, 50_000, 200_000), ("reduce", 40, 50_000, 200_000),
               ("to_list", 100_000, 20, 40), ("keys", 100_000, 20, 40), ("reduce", 100_000, 20, 40)]
WALKS = [(op, "i", k, fz_n, beam_n) for (op, k, fz_n, beam_n) in WALK_SHAPES]


def name(op, kind, k):
    return f"{op}_{kind}_{k}"


def expected(op, k, n):
    if op == "reduce":
        return n * (k * (k - 1) // 2)
    if op in ("to_list", "keys"):
        return n * k
    return sum(PICKS) * n if op in ("get", "case") else k


def fz_key(kind, key):
    return f":{key}" if kind == "a" else f'"{key}"'


def erl_key(kind, key):
    return key if kind == "a" else f'<<"{key}">>'


def fz_source(op, kind, k, n):
    key = lambda i: fz_key(kind, KEYS[i])
    literal = "%{" + ", ".join(f"{key(i)} => {i}" for i in range(k)) + "}"
    if op == "build":
        puts = "".join(f"    m = Map.put(m, {key(i)}, i)\n" for i in range(k))
        return (f"defmodule P do\n  def build(i) do\n    m = %{{}}\n{puts}    m\n  end\n"
                f"  def loop(0, acc), do: acc\n  def loop(n, _acc), do: loop(n - 1, build(n))\nend\n"
                f"dbg(map_size(P.loop({n}, %{{}})))\n")
    if op == "get":
        gets = " + ".join(f"Map.get(m, {key(i)}, 0)" for i in PICKS)
        return (f"defmodule P do\n  def step(m), do: {gets}\n  def loop(0, _m, acc), do: acc\n"
                f"  def loop(n, m, acc), do: loop(n - 1, m, acc + step(m))\nend\ndbg(P.loop({n}, {literal}, 0))\n")
    if op == "case":
        gets = " + ".join(f"at(m, {key(i)})" for i in PICKS)
        return (f"defmodule P do\n  def at(m, k) do\n    case m do\n      %{{^k => v}} -> v\n      _ -> 0\n    end\n  end\n"
                f"  def step(m), do: {gets}\n  def loop(0, _m, acc), do: acc\n"
                f"  def loop(n, m, acc), do: loop(n - 1, m, acc + step(m))\nend\ndbg(P.loop({n}, {literal}, 0))\n")
    if op == "replace":
        body = "".join(f"    m = Map.put(m, {key(i)}, n)\n" for i in PICKS)
    else:
        body = ("".join(f"    m = Map.delete(m, {key(i)})\n" for i in PICKS[:3])
                + "".join(f"    m = Map.put(m, {key(i)}, n)\n" for i in PICKS[:3]))
    return (f"defmodule P do\n  def step(m, n) do\n{body}    m\n  end\n  def loop(0, m), do: m\n"
            f"  def loop(n, m), do: loop(n - 1, step(m, n))\nend\ndbg(map_size(P.loop({n}, {literal})))\n")


WALK_FZ = {"to_list": "length(Map.to_list(m))", "keys": "length(Map.keys(m))",
           "reduce": "Enum.reduce(m, 0, fn ({_k, v}, s) -> s + v end)"}
WALK_ERL = {"to_list": "length(maps:to_list(M))", "keys": "length(maps:keys(M))",
            "reduce": "lists:foldl(fun({_K, V}, S) -> S + V end, 0, maps:to_list(M))"}


def walk_fz_source(op, k, n):
    return (f"defmodule P do\n  def loop(0, _m, acc), do: acc\n"
            f"  def loop(n, m, acc), do: loop(n - 1, m, acc + {WALK_FZ[op]})\nend\n"
            f"m = Map.new(1..{k}, fn (j) -> {{j * 7919, j - 1}} end)\ndbg(P.loop({n}, m, 0))\n")


def walk_erl_source(module, op, k):
    # Elixir's Enum.reduce over a map is :lists.foldl over :maps.to_list.
    return (f"-module({module}).\n-export([main/1]).\n"
            f"loop(0, _M, Acc) -> Acc;\nloop(N, M, Acc) -> loop(N - 1, M, Acc + {WALK_ERL[op]}).\n"
            f"main(N) -> M = maps:from_list([{{J * 7919, J - 1}} || J <- lists:seq(1, {k})]),\n"
            f'    io:format("~p~n", [loop(N, M, 0)]).\n')


def erl_source(module, op, kind, k):
    # The module is fetched at run time: the Erlang compiler folds a chain of maps:put calls with
    # literal keys into one instruction when it can see the callee, and that is a different workload.
    key = lambda i: erl_key(kind, KEYS[i])
    literal = "#{" + ", ".join(f"{key(i)} => {i}" for i in range(k)) + "}"
    head = f"-module({module}).\n-export([main/1]).\n"
    mod = 'list_to_atom(os:getenv("MAP_MODULE"))'
    if op == "build":
        puts = "".join(f"    M{i + 1} = Mod:put({key(i)}, I, M{i}),\n" for i in range(k))
        return (f"{head}build(Mod, I) ->\n    M0 = #{{}},\n{puts}    M{k}.\nloop(_, 0, Acc) -> Acc;\n"
                f"loop(Mod, N, _Acc) -> loop(Mod, N - 1, build(Mod, N)).\n"
                f'main(N) -> io:format("~p~n", [map_size(loop({mod}, N, #{{}}))]).\n')
    if op == "get":
        gets = " + ".join(f"Mod:get({key(i)}, M, 0)" for i in PICKS)
        return (f"{head}step(Mod, M) -> {gets}.\nloop(_, 0, _M, Acc) -> Acc;\n"
                f"loop(Mod, N, M, Acc) -> loop(Mod, N - 1, M, Acc + step(Mod, M)).\n"
                f'main(N) -> io:format("~p~n", [loop({mod}, N, {literal}, 0)]).\n')
    if op == "case":
        gets = " + ".join(f"at(M, {key(i)})" for i in PICKS)
        return (f"{head}at(M, K) ->\n    case M of\n        #{{K := V}} -> V;\n        _ -> 0\n    end.\n"
                f"step(M) -> {gets}.\nloop(0, _M, Acc) -> Acc;\nloop(N, M, Acc) -> loop(N - 1, M, Acc + step(M)).\n"
                f'main(N) -> io:format("~p~n", [loop(N, {literal}, 0)]).\n')
    if op == "replace":
        calls = [f"Mod:put({key(i)}, N, M{j})" for j, i in enumerate(PICKS)]
    else:
        calls = ([f"Mod:remove({key(i)}, M{j})" for j, i in enumerate(PICKS[:3])]
                 + [f"Mod:put({key(i)}, N, M{j + 3})" for j, i in enumerate(PICKS[:3])])
    body = "".join(f"    M{j + 1} = {call},\n" for j, call in enumerate(calls))
    return (f"{head}step(Mod, M0, N) ->\n{body}    M{len(calls)}.\nloop(_, 0, M) -> M;\n"
            f"loop(Mod, N, M) -> loop(Mod, N - 1, step(Mod, M, N)).\n"
            f'main(N) -> io:format("~p~n", [map_size(loop({mod}, N, {literal}))]).\n')


def run(command, **kwargs):
    result = subprocess.run(command, capture_output=True, text=True, **kwargs)
    if result.returncode != 0:
        sys.exit(f"FAILED ({result.returncode}): {' '.join(map(str, command))}\n{result.stdout}{result.stderr}")
    return result


def build(args):
    out, here = os.path.abspath(args.out), os.path.dirname(os.path.abspath(__file__))
    os.makedirs(out, exist_ok=True)
    for op, kind, k, fz_n, _ in PROBES + WALKS:
        walk = kind == "i"
        for n in (fz_n, 2 * fz_n):
            source = os.path.join(out, f"{name(op, kind, k)}_{n}.fz")
            open(source, "w").write(walk_fz_source(op, k, n) if walk else fz_source(op, kind, k, n))
            run([args.fz2, "build", "-o", source[:-3], source])
        module = f"map_{name(op, kind, k)}"
        open(os.path.join(out, f"{module}.erl"), "w").write(
            walk_erl_source(module, op, k) if walk else erl_source(module, op, kind, k))
    names = ", ".join(f'"{key}"' for key in KEYS)
    open(os.path.join(out, "keys.h"), "w").write(
        f"#define KEY_COUNT {len(KEYS)}\nstatic const char *KEY_NAMES[KEY_COUNT] = {{{names}}};\n"
        f"static const int PICKS[6] = {{{', '.join(map(str, PICKS))}}};\n")
    floor = os.path.join(here, "floor")
    run(["cc", "-O2", "-Wall", "-Werror", f"-I{out}", "-o", os.path.join(out, "floor"),
         os.path.join(floor, "harness.c"), os.path.join(floor, "flat.s"), os.path.join(floor, "trie.s"), os.path.join(floor, "walk.s")])
    print(run([os.path.join(out, "floor"), "test"]).stdout.strip(), "(floor agrees with its reference)")


def instructions(command, want, env=None):
    result = run(["/usr/bin/time", "-l"] + command, env=env)
    answer = result.stdout.split()[-1] if result.stdout.split() else ""
    if answer != str(want):
        sys.exit(f"WRONG ANSWER: {' '.join(command)} printed {answer!r}, expected {want}")
    for line in result.stderr.splitlines():
        if "instructions retired" in line:
            return int(line.split()[0])
    sys.exit("no instruction count from /usr/bin/time -l")


def slope(command_for, want_for, n, env=None):
    low = instructions(command_for(n), want_for(n), env)
    high = instructions(command_for(2 * n), want_for(2 * n), env)
    return (high - low) // n


def measure(args):
    out = os.path.abspath(args.out)
    beam = shutil.which("erlc") and shutil.which("erl")
    if beam:
        for op, kind, k, _, _ in PROBES + WALKS:
            run(["erlc", "-o", out, os.path.join(out, f"map_{name(op, kind, k)}.erl")])
    print(f"{'probe':<16}{'fz':>10}{'BEAM':>10}{'floor':>10}{'ordered':>10}")
    for op, kind, k, fz_n, beam_n in PROBES:
        label, want = name(op, kind, k), lambda n: expected(op, k, n)
        row = [slope(lambda n: [os.path.join(out, f"{label}_{n}")], want, fz_n)]
        if beam:
            erl = lambda n: ["erl", "-noshell", "-pa", out, "-eval", f"map_{label}:main({n}), halt()."]
            row.append(slope(erl, want, beam_n, dict(os.environ, MAP_MODULE="maps")))
        else:
            row.append("-")
        floor = lambda n: [os.path.join(out, "floor"), f"{op}_{kind}", str(n), str(k)]
        if k <= FLAT_MAX:
            row.append(slope(floor, want, 1_000_000))
            row.append(slope(floor, want, 1_000_000, dict(os.environ, ORDERED="1")) if kind == "a" else "-")
        elif kind == "a" and op in ("get", "case"):
            row += [slope(floor, want, 1_000_000), "-"]
        else:
            row += ["-", "-"]
        print(f"{label:<16}" + "".join(f"{value:>10}" for value in row), flush=True)
    print(f"\n{'walk':<16}{'fz':>10}{'BEAM':>10}{'floor':>10}   (instructions per entry)")
    for op, kind, k, fz_n, beam_n in WALKS:
        label, want = name(op, kind, k), lambda n: expected(op, k, n)
        row = [slope(lambda n: [os.path.join(out, f"{label}_{n}")], want, fz_n) // k]
        if beam:
            erl = lambda n: ["erl", "-noshell", "-pa", out, "-eval", f"map_{label}:main({n}), halt()."]
            row.append(slope(erl, want, beam_n) // k)
        else:
            row.append("-")
        if op == "reduce":
            row.append("-")
        else:
            floor_n = max(1, 40_000_000 // k)
            floor = lambda n: [os.path.join(out, "floor"), op, str(n), str(k)]
            row.append(slope(floor, lambda n: n * k, floor_n) // k)
        print(f"{label:<16}" + "".join(f"{value:>10}" for value in row), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    b = commands.add_parser("build"); b.add_argument("--fz2", required=True); b.add_argument("--out", required=True)
    m = commands.add_parser("measure"); m.add_argument("--out", required=True)
    args = parser.parse_args()
    build(args) if args.command == "build" else measure(args)


if __name__ == "__main__":
    main()
