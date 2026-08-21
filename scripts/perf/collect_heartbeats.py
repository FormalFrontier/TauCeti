#!/usr/bin/env python3
"""Safely copy advisory heartbeat logs out of an untrusted writable tree.

Candidate Lean code may create arbitrary files and symlinks under ``.lake``.
All source components are therefore opened relative to directory file
descriptors with O_NOFOLLOW. The trusted renderer only sees the copied logs and
a manifest reconstructed from GitHub's trusted changed-file metadata.
"""

from __future__ import annotations

import argparse
import json
import os
import stat
from pathlib import Path


MAX_LOG_BYTES = 10 * 1024 * 1024


def read_beneath(root: Path, parts: tuple[str, ...]) -> bytes | None:
    root_fd = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    directory_fd = root_fd
    try:
        try:
            for part in parts[:-1]:
                next_fd = os.open(
                    part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                    dir_fd=directory_fd,
                )
                if directory_fd != root_fd:
                    os.close(directory_fd)
                directory_fd = next_fd
            file_fd = os.open(
                parts[-1], os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW,
                dir_fd=directory_fd,
            )
        except FileNotFoundError:
            return None
        try:
            if not stat.S_ISREG(os.fstat(file_fd).st_mode):
                raise ValueError(f"heartbeat output is not a regular file: {'/'.join(parts)}")
            data = os.read(file_fd, MAX_LOG_BYTES + 1)
        finally:
            os.close(file_fd)
        if len(data) > MAX_LOG_BYTES:
            raise ValueError(f"heartbeat log exceeds {MAX_LOG_BYTES} bytes: {'/'.join(parts)}")
        return data
    finally:
        if directory_fd != root_fd:
            os.close(directory_fd)
        os.close(root_fd)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake-root", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    entries = json.loads(args.manifest.read_text())
    rows: list[str] = []
    copied = 0
    for entry in entries:
        kind, slug = entry["kind"], entry["slug"]
        sides: tuple[str, ...]
        if kind == "added":
            sides = ("added",)
            rows.append(f"added\t{slug}\t{entry['head_path']}")
        elif kind == "modified":
            sides = ("base", "head")
            rows.append(f"modified\t{slug}\t{entry['head_path']}")
        else:
            continue
        for side in sides:
            data = read_beneath(
                args.lake_root,
                ("tmp", "profile", "src", side, f"{slug}.hb"),
            )
            if data is None:
                continue
            destination = args.output / "src" / side / f"{slug}.hb"
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
            copied += 1
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "manifest.tsv").write_text("\n".join(rows) + ("\n" if rows else ""))
    print(f"Safely collected {copied} heartbeat log(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
