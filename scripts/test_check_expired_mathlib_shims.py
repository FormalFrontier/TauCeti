#!/usr/bin/env python3
"""Regression tests for ``scripts/check-expired-mathlib-shims.py``."""

from __future__ import annotations

import importlib.util
import json
import pathlib
import sys
import tempfile
import unittest
from unittest import mock


SCRIPT = pathlib.Path(__file__).with_name("check-expired-mathlib-shims.py")
SPEC = importlib.util.spec_from_file_location("check_expired_mathlib_shims", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
check = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = check
SPEC.loader.exec_module(check)


class ExpiredMathlibShimTests(unittest.TestCase):
    def test_registry_covers_self_declarations_one_way(self):
        root = SCRIPT.parent.parent
        groups = check.load_registry(root / "TauCeti/mathlib-shims.json", root)
        tracked = {source for group in groups for source in group.sources}
        self.assertLessEqual(check.find_self_declared_shims(root / "TauCeti"), tracked)
        self.assertEqual(groups[0].declarations,
                         ("Complex.exists_bijOn_unitBall_map_eq_zero",))
        for group in groups:
            if group.speculative or group.landing_sentinel:
                continue
            declared = set().union(*(
                check.source_declarations(root / source) for source in group.sources
            ))
            self.assertLessEqual(set(group.local_declarations), declared)
        check.validate_registry_coverage(groups, root / "TauCeti")

    def test_new_self_declaration_requires_registry_entry(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            source_root = root / "TauCeti"
            source_root.mkdir()
            (source_root / "New.lean").write_text(
                "These declarations are a temporary shim pending Mathlib.", encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError, "TauCeti/New.lean"):
                check.validate_registry_coverage((), source_root)

    def test_negated_temporary_shim_is_not_a_self_declaration(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            source_root = root / "TauCeti"
            source_root.mkdir()
            (source_root / "New.lean").write_text(
                "This is new formalization rather than a temporary shim.", encoding="utf-8"
            )
            self.assertEqual(check.find_self_declared_shims(source_root), set())

    def test_explicit_mathlib_deletion_is_a_self_declaration(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            source_root = root / "TauCeti"
            source_root.mkdir()
            (source_root / "New.lean").write_text(
                "When Mathlib bumps past the upstream PR, this file is deleted outright.",
                encoding="utf-8",
            )
            self.assertEqual(
                check.find_self_declared_shims(source_root),
                {pathlib.Path("TauCeti/New.lean")},
            )

    def test_vendored_migrate_and_delete_is_a_self_declaration(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            source_root = root / "TauCeti"
            source_root.mkdir()
            (source_root / "New.lean").write_text(
                "Vendored from mathlib4#1; migrate to Mathlib and delete this file when it merges.",
                encoding="utf-8",
            )
            self.assertEqual(
                check.find_self_declared_shims(source_root),
                {pathlib.Path("TauCeti/New.lean")},
            )

    def test_ported_copy_deleted_for_mathlib_is_a_self_declaration(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            source_root = root / "TauCeti"
            source_root.mkdir()
            (source_root / "New.lean").write_text(
                "This copy is deleted in favour of the Mathlib declarations once the PR lands.",
                encoding="utf-8",
            )
            self.assertEqual(
                check.find_self_declared_shims(source_root),
                {pathlib.Path("TauCeti/New.lean")},
            )

    def test_bold_negation_is_not_a_self_declaration(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            source_root = root / "TauCeti"
            source_root.mkdir()
            (source_root / "New.lean").write_text(
                "This is **not** a temporary shim.", encoding="utf-8"
            )
            self.assertEqual(check.find_self_declared_shims(source_root), set())

    def test_registry_rejects_missing_source_and_malformed_target(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps([{
                "sources": ["TauCeti/Missing.lean"],
                "declarations": ["not a Lean name"],
            }]), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "invalid declaration"):
                check.load_registry(manifest, root)

    def test_registry_rejects_parent_path(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps([{
                "sources": ["TauCeti/../Outside.lean"],
                "declarations": ["Future.name"],
            }]), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "TauCeti/.*path"):
                check.load_registry(manifest, root)

    def test_exact_declaration_probe_requires_local_surface(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            (root / "TauCeti").mkdir()
            (root / "TauCeti/Old.lean").touch()
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps([{
                "sources": ["TauCeti/Old.lean"],
                "declarations": ["Upstream.done"],
            }]), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "require local_declarations"):
                check.load_registry(manifest, root)

    def test_exact_module_probe_requires_local_surface(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            (root / "TauCeti").mkdir()
            (root / "TauCeti/Old.lean").touch()
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps([{
                "sources": ["TauCeti/Old.lean"],
                "modules": ["Mathlib.New"],
            }]), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "require local_declarations"):
                check.load_registry(manifest, root)

    def test_base_registry_obligation_is_ratcheted_until_local_surface_moves(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            source = pathlib.Path("TauCeti/Old.lean")
            (root / source).parent.mkdir()
            (root / source).write_text("lemma oldShim : True := by trivial\n", encoding="utf-8")
            base = check.ShimGroup(
                (source,), ("Upstream.done",), (), "base",
                local_declarations=("oldShim",),
            )
            with self.assertRaisesRegex(ValueError, "base shim obligations"):
                check.validate_registry_ratchet((), (base,), root)
            kept = check.ShimGroup(
                (source,), ("Upstream.done", "Future.more"), (), "kept",
                local_declarations=("oldShim",),
            )
            check.validate_registry_ratchet((kept,), (base,), root)
            weakened = check.ShimGroup(
                (source,), ("Upstream.done",), (), "weakened", landing_sentinel=True,
                local_declarations=("oldShim",),
            )
            with self.assertRaisesRegex(ValueError, "audit-only sentinel"):
                check.validate_registry_ratchet((weakened,), (base,), root)
            moved = root / "TauCeti/Moved.lean"
            (root / source).rename(moved)
            with self.assertRaisesRegex(ValueError, "base shim obligations"):
                check.validate_registry_ratchet((), (base,), root)
            moved.unlink()
            (root / source).touch()
            (root / source).write_text("lemma stillUseful : True := by trivial\n", encoding="utf-8")
            check.validate_registry_ratchet((), (base,), root)

    def test_only_new_or_changed_groups_ignores_unchanged_base_entries(self):
        one = pathlib.Path("TauCeti/One.lean")
        two = pathlib.Path("TauCeti/Two.lean")
        base = check.ShimGroup(
            (one,), ("Upstream.one",), (), "base", local_declarations=("one",)
        )
        unchanged = check.dataclasses.replace(base, note="note edits are not new obligations")
        added = check.ShimGroup(
            (two,), ("Upstream.two",), (), "added", local_declarations=("two",)
        )
        self.assertEqual(check.only_new_or_changed_groups((unchanged, added), (base,)), (added,))

    def test_probe_round_trip(self):
        source = check.render_declaration_probe(["Foo.bar", "Alpha", "Foo.bar"])
        self.assertEqual(source.count("env.contains `Foo.bar"), 1)
        self.assertIn("env.contains `Alpha", source)
        output = "noise\n" + check.PROBE_PREFIX + "Foo.bar\n"
        self.assertEqual(check.parse_probe_output(output), {"Foo.bar"})

    def test_empty_declaration_probe_does_not_launch_lean(self):
        with mock.patch.object(check.subprocess, "run") as run:
            self.assertEqual(check.probe_declarations((), pathlib.Path(".")), set())
        run.assert_not_called()

    def test_declaration_and_module_replacements_render_report_and_gate(self):
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
            blocking = check.markdown_summary((group,), available, blocking=True)
            self.assertIn("PR is blocked until its worker migrates", blocking)
            self.assertIn("TauCeti/One.lean", summary)
            self.assertIn("test group", summary)

    def test_speculative_target_is_labeled(self):
        group = check.ShimGroup(
            (pathlib.Path("TauCeti/One.lean"),), ("Future.name",), (), "not named", True
        )
        available = check.available_replacements((group,), {"Future.name"}, pathlib.Path("."))
        summary = check.markdown_summary((group,), available)
        self.assertIn("Speculative target name", summary)

    def test_landing_sentinel_requires_audit_not_source_deletion(self):
        group = check.ShimGroup(
            (pathlib.Path("TauCeti/Mixed.lean"),),
            ("Upstream.sentinel",),
            (),
            "mixed source",
            landing_sentinel=True,
        )
        available = check.available_replacements(
            (group,), {"Upstream.sentinel"}, pathlib.Path(".")
        )
        summary = check.markdown_summary((group,), available)
        warning = check.warning_message(available[0])
        self.assertIn("migrate only declarations with canonical counterparts", summary)
        self.assertIn("preserve or re-home source-only API", warning)
        self.assertNotIn("delete this file", summary + warning)
        self.assertFalse(check.blocks_bump(available[0]))
        exact = check.AvailableReplacement(
            pathlib.Path("TauCeti/Exact.lean"), ("declaration Upstream.exact",), "exact"
        )
        self.assertTrue(check.blocks_bump(exact))

    def test_missing_mathlib_tree_rejects_module_checks(self):
        group = check.ShimGroup(
            (pathlib.Path("TauCeti/One.lean"),), (), ("Mathlib.Topology.NewThing",), "test"
        )
        with tempfile.TemporaryDirectory() as temporary:
            missing = pathlib.Path(temporary) / "missing"
            with self.assertRaisesRegex(RuntimeError, "Mathlib source tree does not exist"):
                check.available_replacements((group,), set(), missing)

    def test_fail_on_available_is_the_bump_worker_gate(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            source_root = root / "TauCeti"
            source_root.mkdir()
            (source_root / "Old.lean").write_text(
                "This is a temporary Mathlib shim.", encoding="utf-8"
            )
            manifest = source_root / "mathlib-shims.json"
            manifest.write_text(json.dumps([{
                "sources": ["TauCeti/Old.lean"],
                "declarations": ["Upstream.done"],
                "local_declarations": ["oldShim"],
                "note": "exact replacement",
            }]), encoding="utf-8")
            common = ["--repo-root", str(root), "--manifest", str(manifest)]
            with mock.patch.object(check, "probe_declarations", return_value={"Upstream.done"}):
                self.assertEqual(check.main(common), 0)
                self.assertEqual(check.main([*common, "--fail-on-available"]), 3)

    def test_unexpected_checker_failure_is_infrastructure_not_migration(self):
        with mock.patch.object(check, "load_registry", side_effect=OSError("bad bytes")):
            self.assertEqual(check.main([]), 2)

if __name__ == "__main__":
    unittest.main()
