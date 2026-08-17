#!/usr/bin/env python3
"""Regression tests for ``scripts/check-expired-mathlib-shims.py``."""

from __future__ import annotations

import importlib.util
import json
import pathlib
import sys
import tempfile
import unittest


SCRIPT = pathlib.Path(__file__).with_name("check-expired-mathlib-shims.py")
SPEC = importlib.util.spec_from_file_location("check_expired_mathlib_shims", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
check = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = check
SPEC.loader.exec_module(check)


class ExpiredMathlibShimTests(unittest.TestCase):
    def test_registry_tracks_the_issue_baseline(self):
        root = SCRIPT.parent.parent
        groups = check.load_registry(SCRIPT.with_name("mathlib-shims.json"), root)
        self.assertEqual(sum(len(group.sources) for group in groups), 35)
        self.assertEqual(groups[0].declarations, ("exists_bijOn_unitBall_map_eq_zero",))
        check.validate_registry_coverage(groups, root / "TauCeti")

    def test_new_self_declaration_requires_registry_entry(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            source_root = root / "TauCeti"
            source_root.mkdir()
            (source_root / "New.lean").write_text(
                "This is temporary while the matching result is pending in Mathlib."
            )
            with self.assertRaisesRegex(ValueError, "TauCeti/New.lean"):
                check.validate_registry_coverage((), source_root)

    def test_registry_rejects_missing_source_and_malformed_target(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps([{
                "sources": ["TauCeti/Missing.lean"],
                "declarations": ["not a Lean name"],
            }]))
            with self.assertRaisesRegex(ValueError, "invalid declaration"):
                check.load_registry(manifest, root)

    def test_probe_round_trip(self):
        source = check.render_declaration_probe(["Foo.bar", "Alpha", "Foo.bar"])
        self.assertEqual(source.count("env.contains `Foo.bar"), 1)
        self.assertIn("env.contains `Alpha", source)
        output = "noise\n" + check.PROBE_PREFIX + "Foo.bar\n"
        self.assertEqual(check.parse_probe_output(output), {"Foo.bar"})

    def test_declaration_and_module_replacements_are_report_only(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            module = root / "Mathlib/Topology/NewThing.lean"
            module.parent.mkdir(parents=True)
            module.touch()
            group = check.ShimGroup(
                (pathlib.Path("TauCeti/One.lean"), pathlib.Path("TauCeti/Two.lean")),
                ("New.theorem", "Still.missing"),
                ("Mathlib.Topology.NewThing", "Mathlib.Topology.Missing"),
                "test group",
            )
            available = check.available_replacements((group,), {"New.theorem"}, root)
            self.assertEqual(len(available), 2)
            self.assertEqual(available[0].targets, (
                "declaration New.theorem", "module Mathlib.Topology.NewThing"))
            summary = check.markdown_summary((group,), available)
            self.assertIn("report does not fail the build", summary)
            self.assertIn("TauCeti/One.lean", summary)


if __name__ == "__main__":
    unittest.main()
