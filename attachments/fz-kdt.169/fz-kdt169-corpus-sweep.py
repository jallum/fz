#!/usr/bin/env python3
from __future__ import annotations

import concurrent.futures
import os
from pathlib import Path
import re
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
print_lock = threading.Lock()


def fixture_key(path: Path) -> str:
    return "__".join(path.relative_to(ROOT).parts).removesuffix(".fz")


def normalized(data: bytes, side: str, aot: Path) -> bytes:
    text = data.decode("utf-8", errors="replace")
    text = re.sub(r"thread '[^']+' \(\d+\)", "thread '<name>' (<id>)", text)
    text = re.sub(r"0x[0-9a-fA-F]+", "0x<addr>", text)
    text = text.replace(str(SIDES[side]), "<FZ2>")
    text = text.replace(str(aot), "<AOT>")
    return text.encode()


def run(command: list[str], side: str, aot: Path) -> tuple[int, bytes, bytes]:
    process = subprocess.Popen(
        command,
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=TIMEOUT_SECONDS)
        return process.returncode, normalized(stdout, side, aot), normalized(stderr, side, aot)
    except subprocess.TimeoutExpired as error:
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
        stdout = stdout or error.stdout or b""
        stderr = (stderr or error.stderr or b"") + b"\n<timeout>\n"
        return 124, normalized(stdout, side, aot), normalized(stderr, side, aot)


def write_result(prefix: Path, result: tuple[int, bytes, bytes]) -> None:
    rc, stdout, stderr = result
    Path(f"{prefix}.rc").write_text(f"{rc}\n")
    Path(f"{prefix}.out").write_bytes(stdout)
    Path(f"{prefix}.err").write_bytes(stderr)


def sweep_side(side: str, fixture: Path) -> None:
    binary = SIDES[side]
    side_dir = OUT / side
    key = fixture_key(fixture)
    aot = side_dir / f"{key}.aot"
    backend = side_dir / f"{key}.backend"
    activations = side_dir / f"{key}.activations"
    write_result(
        side_dir / f"{key}.interp",
        run(
            [str(binary), "interp", "--dump", f"backend={backend}", "--dump", f"activations={activations}", str(fixture)],
            side,
            aot,
        ),
    )
    write_result(side_dir / f"{key}.run", run([str(binary), "run", str(fixture)], side, aot))
    build = run([str(binary), "build", str(fixture), "-o", str(aot)], side, aot)
    write_result(side_dir / f"{key}.build", build)
    if build[0] == 0 and aot.is_file():
        aot_result = run([str(aot)], side, aot)
    else:
        aot_result = (125, b"", b"<not-built>\n")
    write_result(side_dir / f"{key}.aot-run", aot_result)


def sweep_fixture(index_fixture: tuple[int, Path]) -> None:
    index, fixture = index_fixture
    for side in SIDES:
        sweep_side(side, fixture)
    if index % 20 == 0:
        with print_lock:
            print(f"completed {index}/{len(FIXTURES)} {fixture.relative_to(ROOT)}", flush=True)


FIXTURES = sorted(ROOT.glob("fixtures2/**/*.fz"))
if len(FIXTURES) != 607:
    raise SystemExit(f"expected 607 fixtures, found {len(FIXTURES)}")
for side, binary in SIDES.items():
    if not binary.is_file():
        raise SystemExit(f"missing {side} binary: {binary}")
(OUT / "fixtures.txt").write_text("".join(f"{path.relative_to(ROOT)}\n" for path in FIXTURES))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
    list(executor.map(sweep_fixture, enumerate(FIXTURES, start=1)))
print("sweep complete", flush=True)
