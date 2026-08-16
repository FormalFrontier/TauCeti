#!/usr/bin/env python3
"""Measure changed Lean modules with host perf around an offline landrun."""

from __future__ import annotations

import argparse
import json
import os
import signal
import stat
import subprocess
import sys
import time
from pathlib import Path


OUTER_TIMEOUT = 370


def terminate_group(process: subprocess.Popen[bytes]) -> None:
    try:
        os.killpg(process.pid, signal.SIGTERM)
        process.wait(timeout=10)
    except (ProcessLookupError, subprocess.TimeoutExpired):
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def run(command: list[str], *, cwd: Path, timeout: int | None = None) -> int:
    process = subprocess.Popen(command, cwd=cwd, start_new_session=True)
    try:
        return process.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        terminate_group(process)
        return 124


def sandbox_command(
    root: Path, landrun: str, watchdog_toolchain: Path, modules: list[str]
) -> list[str]:
    command = [
        landrun,
        "--rox", "/usr", "--rox", "/etc",
        "--rw", "/dev/null", "--rox", "/dev/zero", "--rox", "/dev/urandom", "--rox", "/dev/random",
        "--rox", str(Path.home() / ".elan"), "--rox", str(watchdog_toolchain),
        "--rox", str(root), "--rw", str(root / ".lake"),
    ]
    for name in (
        "PATH", "HOME", "CI", "LAKE_NO_CACHE", "LAKE_ARTIFACT_CACHE",
        "LAKE_RESTORE_ARTIFACTS", "LAKE_CACHE_DIR", "WATCHDOG_TOOLCHAIN",
    ):
        command.extend(("--env", name))
    command.extend(
        (
            "--", "bash", "-euo", "pipefail", "-c",
            'export LAKE_OVERRIDE_LEAN=true; export LEAN="$WATCHDOG_TOOLCHAIN/bin/lean"; exec lake build "$@"',
            "_", *modules,
        )
    )
    return command


def parse_instructions(path: Path) -> int | None:
    if not path.exists():
        return None
    for line in path.read_text(errors="replace").splitlines():
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            continue
        event = str(record.get("event", ""))
        if event not in {"instructions", "instructions:u"}:
            continue
        raw = str(record.get("counter-value", "")).replace(",", "")
        try:
            return int(float(raw))
        except ValueError:
            return None
    return None


def parse_cpu_seconds(path: Path) -> float | None:
    if not path.exists():
        return None
    try:
        record = json.loads(path.read_text())
        return float(record["user_seconds"]) + float(record["system_seconds"])
    except (json.JSONDecodeError, KeyError, TypeError, ValueError):
        return None


def invalidate_module(root: Path, source_path: str) -> None:
    """Remove only this module's Lake outputs so the timed build must run Lean."""
    relative = Path(source_path).with_suffix("")
    for fixed in (("build", "lib", "lean"), ("build", "ir")):
        root_fd = os.open(root / ".lake", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        directory_fd = root_fd
        try:
            try:
                for part in (*fixed, *relative.parent.parts):
                    next_fd = os.open(
                        part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                        dir_fd=directory_fd,
                    )
                    if directory_fd != root_fd:
                        os.close(directory_fd)
                    directory_fd = next_fd
            except FileNotFoundError:
                continue
            prefix = relative.name + "."
            for name in os.listdir(directory_fd):
                if not name.startswith(prefix):
                    continue
                mode = os.stat(name, dir_fd=directory_fd, follow_symlinks=False).st_mode
                if stat.S_ISREG(mode) or stat.S_ISLNK(mode):
                    os.unlink(name, dir_fd=directory_fd)
                else:
                    raise RuntimeError(f"unexpected non-file module output: {name}")
        finally:
            if directory_fd != root_fd:
                os.close(directory_fd)
            os.close(root_fd)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--side", choices=("base", "head"), required=True)
    parser.add_argument("--raw-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--landrun", default="landrun")
    parser.add_argument("--watchdog-toolchain", type=Path, required=True)
    parser.add_argument("--perf", default="perf")
    parser.add_argument("--metric", choices=("instructions", "cpu"), required=True)
    args = parser.parse_args()

    root = args.root.resolve()
    watchdog_toolchain = args.watchdog_toolchain.resolve()
    if not (watchdog_toolchain / "bin" / "lean").is_file():
        raise SystemExit("missing prepared watchdog toolchain")
    os.environ["WATCHDOG_TOOLCHAIN"] = str(watchdog_toolchain)
    entries = json.loads(args.manifest.read_text())
    selected = [
        entry for entry in entries
        if (args.side == "head" and entry["kind"] in {"added", "modified"})
        or (args.side == "base" and entry["kind"] == "modified")
    ]
    modules = list(dict.fromkeys(entry[f"{args.side}_module"] for entry in selected))
    results: list[dict[str, object]] = []
    args.raw_dir.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)

    if modules:
        # Make every selected source newer than inherited artifacts, then build the
        # full changed set once so each timed rebuild has an already-built dependency cone.
        for entry in selected:
            source = root / entry[f"{args.side}_path"]
            if source.is_symlink() or not source.is_file() or root not in source.resolve().parents:
                raise SystemExit(f"unsafe or missing source: {source}")
            source.touch()
        prebuild = run(
            sandbox_command(root, args.landrun, watchdog_toolchain, modules), cwd=root
        )
        if prebuild != 0:
            print(f"{args.side} prebuild failed with exit code {prebuild}", file=sys.stderr)
            for entry in selected:
                results.append(
                    {
                        "slug": entry["slug"],
                        "module": entry[f"{args.side}_module"],
                        "status": "failed",
                        "returncode": prebuild,
                        "metric": args.metric,
                        "value": None,
                        "wall_seconds": None,
                    }
                )
            args.output.write_text(json.dumps(results, indent=2) + "\n")
            return 1

    # The prebuild may restore trusted dependency artifacts, but the isolated
    # measurement itself must actually invoke Lean for the selected module.
    os.environ["LAKE_ARTIFACT_CACHE"] = "false"
    os.environ["LAKE_RESTORE_ARTIFACTS"] = "false"
    os.environ["LAKE_CACHE_DIR"] = ""

    for entry in selected:
        source = root / entry[f"{args.side}_path"]
        module = entry[f"{args.side}_module"]
        invalidate_module(root, entry[f"{args.side}_path"])
        raw = args.raw_dir / f"{entry['slug']}.json"
        measured = sandbox_command(root, args.landrun, watchdog_toolchain, [module])
        if args.metric == "instructions":
            command = [
                args.perf, "stat", "-j", "-e", "instructions:u", "-o", str(raw), "--",
                *measured,
            ]
        else:
            command = [
                "/usr/bin/time", "--quiet",
                "--format", '{"user_seconds":%U,"system_seconds":%S,"wall_seconds":%e}',
                "--output", str(raw), "--", *measured,
            ]
        started = time.monotonic()
        returncode = run(command, cwd=root, timeout=OUTER_TIMEOUT)
        elapsed = time.monotonic() - started
        value = parse_instructions(raw) if args.metric == "instructions" else parse_cpu_seconds(raw)
        status = "ok" if returncode == 0 and value is not None else "failed"
        results.append(
            {
                "slug": entry["slug"], "module": module, "status": status,
                "returncode": returncode, "metric": args.metric, "value": value,
                "wall_seconds": round(elapsed, 3),
            }
        )

    args.output.write_text(json.dumps(results, indent=2) + "\n")
    failures = sum(result["status"] != "ok" for result in results)
    print(f"Measured {len(results)} {args.side} module(s); {failures} failed")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
