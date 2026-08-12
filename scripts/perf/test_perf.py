#!/usr/bin/env python3
"""Regression tests for the trusted Lean performance-gate boundary.

The cases live together because they exercise the gate's cross-cutting safety
contract: watchdog discovery and termination, instruction/CPU reporting
thresholds, changed-file manifest construction, and no-follow handling of
outputs and build trees that untrusted Lean code can modify inside landrun.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from scripts.perf.measure import invalidate_module


HERE = Path(__file__).resolve().parent


class WatchdogTests(unittest.TestCase):
    def make_toolchain(self, directory: str) -> Path:
        root = Path(directory)
        (root / "bin").mkdir()
        (root / "bin" / "lean").write_bytes((HERE / "lean-watchdog.sh").read_bytes())
        (root / "bin" / "lean").chmod(0o755)
        (root / "bin" / "lean-real").symlink_to("/bin/sh")
        return root

    def test_lake_probe_reports_wrapper_root(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = self.make_toolchain(directory)
            result = subprocess.run(
                [root / "bin" / "lean", "--print-prefix"],
                text=True, capture_output=True,
            )
            self.assertEqual(result.returncode, 0)
            self.assertEqual(result.stdout.strip(), str(root))

    def test_forwards_exit_code(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = self.make_toolchain(directory)
            result = subprocess.run([root / "bin" / "lean", "-c", "exit 17"])
            self.assertEqual(result.returncode, 17)

    def test_times_out_process_group(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = self.make_toolchain(directory)
            env = dict(
                os.environ, TAUCETI_LEAN_TIMEOUT_SECONDS="0.1",
                TAUCETI_LEAN_KILL_GRACE_SECONDS="0.1",
            )
            result = subprocess.run(
                [root / "bin" / "lean", "-c", "trap '' TERM; sleep 20"],
                env=env, text=True, capture_output=True, timeout=3,
            )
            self.assertIn(result.returncode, (124, 137))
            self.assertIn("exceeded the 0.1s wall-clock limit", result.stderr)


class ReportTests(unittest.TestCase):
    def run_report(self, base_value: int, head_value: int) -> int:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "manifest.json").write_text(json.dumps([
                {"kind": "modified", "slug": "f0000", "head_path": "TauCeti/X.lean"}
            ]))
            for side, value in (("base", base_value), ("head", head_value)):
                (root / f"{side}.json").write_text(json.dumps([
                    {"slug": "f0000", "status": "ok", "metric": "instructions", "value": value}
                ]))
            return subprocess.run([
                sys.executable, HERE / "report.py", "--manifest", root / "manifest.json",
                "--base", root / "base.json", "--head", root / "head.json",
                "--output", root / "report.md", "--metric", "instructions",
            ]).returncode

    def test_requires_both_modified_thresholds(self) -> None:
        self.assertEqual(self.run_report(100_000_000_000, 160_000_000_000), 0)
        self.assertEqual(self.run_report(300_000_000_000, 410_000_000_000), 0)
        self.assertEqual(self.run_report(200_000_000_000, 310_000_000_000), 1)

    def test_new_file_absolute_limit(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "manifest.json").write_text(json.dumps([
                {"kind": "added", "slug": "f0000", "head_path": "TauCeti/New.lean"}
            ]))
            (root / "base.json").write_text("[]")
            for value, expected in ((499_999_999_999, 0), (500_000_000_000, 1)):
                (root / "head.json").write_text(json.dumps([
                    {"slug": "f0000", "status": "ok", "metric": "instructions", "value": value}
                ]))
                result = subprocess.run([
                    sys.executable, HERE / "report.py", "--manifest", root / "manifest.json",
                    "--base", root / "base.json", "--head", root / "head.json",
                    "--output", root / "report.md", "--metric", "instructions",
                ])
                self.assertEqual(result.returncode, expected)

    def test_cpu_fallback_thresholds(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "manifest.json").write_text(json.dumps([
                {"kind": "modified", "slug": "f0000", "head_path": "TauCeti/X.lean"}
            ]))
            (root / "base.json").write_text(json.dumps([
                {"slug": "f0000", "status": "ok", "metric": "cpu", "value": 50.0}
            ]))
            for value, expected in ((79.0, 0), (80.0, 1)):
                (root / "head.json").write_text(json.dumps([
                    {"slug": "f0000", "status": "ok", "metric": "cpu", "value": value}
                ]))
                result = subprocess.run([
                    sys.executable, HERE / "report.py", "--manifest", root / "manifest.json",
                    "--base", root / "base.json", "--head", root / "head.json",
                    "--output", root / "report.md", "--metric", "cpu",
                ])
                self.assertEqual(result.returncode, expected)


class ManifestTests(unittest.TestCase):
    def test_rename_preserves_base_path(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            base, head = root / "base", root / "head"
            (base / "TauCeti").mkdir(parents=True)
            (head / "TauCeti").mkdir(parents=True)
            (base / "TauCeti" / "Old.lean").write_text("def old := 1\n")
            (head / "TauCeti" / "New.lean").write_text("def new := 1\n")
            (root / "files.json").write_text(json.dumps([
                {"status": "renamed", "filename": "TauCeti/New.lean",
                 "previous_filename": "TauCeti/Old.lean"}
            ]))
            subprocess.run([
                sys.executable, HERE / "manifest.py", "--files", root / "files.json",
                "--base", base, "--head", head, "--output", root / "manifest.json",
            ], check=True)
            entry = json.loads((root / "manifest.json").read_text())[0]
            self.assertEqual(entry["base_module"], "TauCeti.Old")
            self.assertEqual(entry["head_module"], "TauCeti.New")


class HeartbeatCollectionTests(unittest.TestCase):
    def test_refuses_symlinked_sandbox_output_ancestor(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            lake = root / ".lake"
            lake.mkdir()
            (root / "outside").mkdir()
            (lake / "tmp").symlink_to(root / "outside", target_is_directory=True)
            (root / "manifest.json").write_text(json.dumps([
                {"kind": "added", "slug": "f0000", "head_path": "TauCeti/New.lean"}
            ]))
            result = subprocess.run([
                sys.executable, HERE / "collect_heartbeats.py", "--lake-root", lake,
                "--manifest", root / "manifest.json", "--output", root / "collected",
            ], text=True, capture_output=True)
            self.assertNotEqual(result.returncode, 0)

    def test_module_invalidation_refuses_symlinked_build_tree(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / ".lake").mkdir()
            outside = root / "outside"
            outside.mkdir()
            victim = outside / "X.olean"
            victim.write_text("keep")
            (root / ".lake" / "build").symlink_to(outside, target_is_directory=True)
            with self.assertRaises(OSError):
                invalidate_module(root, "X.lean")
            self.assertEqual(victim.read_text(), "keep")


if __name__ == "__main__":
    unittest.main()
