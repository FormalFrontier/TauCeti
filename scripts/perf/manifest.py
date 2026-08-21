#!/usr/bin/env python3
"""Turn GitHub's trusted changed-file JSON into a safe performance manifest."""

from __future__ import annotations

import argparse
import json
import shutil
from pathlib import Path, PurePosixPath


def lean_path(raw: object) -> str | None:
    if not isinstance(raw, str):
        raise ValueError("changed-file path is not a string")
    if any(ord(char) < 32 for char in raw):
        raise ValueError(f"changed-file path contains a control character: {raw!r}")
    path = PurePosixPath(raw)
    if path.is_absolute() or ".." in path.parts:
        raise ValueError(f"unsafe changed-file path: {raw!r}")
    if raw == "TauCeti.lean" or (raw.startswith("TauCeti/") and raw.endswith(".lean")):
        if "`" in raw or "|" in raw:
            raise ValueError(f"Lean path contains unsafe report punctuation: {raw!r}")
        return raw
    return None


def module_name(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def regular_file(root: Path, relative: str) -> Path:
    path = root / relative
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"expected a regular Lean file: {path}")
    if root.resolve() not in path.resolve().parents:
        raise ValueError(f"Lean file escapes checkout: {path}")
    return path


def flatten_files(value: object) -> list[dict[str, object]]:
    if isinstance(value, dict):
        value = value.get("files")
    if not isinstance(value, list):
        raise ValueError("changed-file JSON is not a list")
    if value and all(isinstance(page, list) for page in value):
        value = [item for page in value for item in page]
    if not all(isinstance(item, dict) for item in value):
        raise ValueError("changed-file JSON contains a non-object entry")
    return value  # type: ignore[return-value]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--files", type=Path, required=True)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--head", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--heartbeat-dir", type=Path)
    args = parser.parse_args()

    files = flatten_files(json.loads(args.files.read_text()))
    if len(files) >= 3000:
        raise SystemExit("changed-file list hit GitHub's 3000-file cap; failing closed")

    entries: list[dict[str, str]] = []
    for index, item in enumerate(files):
        status = item.get("status")
        head_path = lean_path(item.get("filename"))
        if head_path is None:
            continue
        slug = f"f{index:04d}"
        if status == "removed":
            entries.append({"kind": "removed", "slug": slug, "base_path": head_path})
            continue
        if status in {"added", "copied"}:
            regular_file(args.head, head_path)
            entries.append(
                {"kind": "added", "slug": slug, "head_path": head_path,
                 "head_module": module_name(head_path)}
            )
            continue
        base_path = head_path
        if status == "renamed":
            previous = lean_path(item.get("previous_filename"))
            if previous is None:
                raise ValueError(f"renamed Lean file lacks a safe previous path: {head_path}")
            base_path = previous
        regular_file(args.base, base_path)
        regular_file(args.head, head_path)
        entries.append(
            {"kind": "modified", "slug": slug, "base_path": base_path,
             "base_module": module_name(base_path), "head_path": head_path,
             "head_module": module_name(head_path)}
        )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(entries, indent=2) + "\n")

    if args.heartbeat_dir is not None:
        prep = args.heartbeat_dir
        shutil.rmtree(prep, ignore_errors=True)
        for side in ("added", "base", "head"):
            (prep / "src" / side).mkdir(parents=True, exist_ok=True)
        rows: list[str] = []
        for entry in entries:
            kind, slug = entry["kind"], entry["slug"]
            if kind == "added":
                shutil.copyfile(args.head / entry["head_path"], prep / "src" / "added" / f"{slug}.lean")
                rows.append(f"added\t{slug}\t{entry['head_path']}")
            elif kind == "modified":
                shutil.copyfile(args.base / entry["base_path"], prep / "src" / "base" / f"{slug}.lean")
                shutil.copyfile(args.head / entry["head_path"], prep / "src" / "head" / f"{slug}.lean")
                rows.append(f"modified\t{slug}\t{entry['head_path']}")
        (prep / "manifest.tsv").write_text("\n".join(rows) + ("\n" if rows else ""))

    print(f"Prepared {len(entries)} Lean file change(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
