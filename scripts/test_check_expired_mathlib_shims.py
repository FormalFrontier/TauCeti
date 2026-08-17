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


class FakeZulip:
    def __init__(self, messages=()):
        self.messages = list(messages)
        self.narrows = []
        self.sent = []
        self.updated = []

    def my_user_id(self):
        return 7

    def get_messages(self, narrow):
        self.narrows.append(narrow)
        return self.messages

    def send_message(self, content):
        self.sent.append(content)

    def update_message(self, message_id, content):
        self.updated.append((message_id, content))


class ExpiredMathlibShimTests(unittest.TestCase):
    def test_registry_covers_self_declarations_one_way(self):
        root = SCRIPT.parent.parent
        groups = check.load_registry(SCRIPT.with_name("mathlib-shims.json"), root)
        tracked = {source for group in groups for source in group.sources}
        self.assertLessEqual(check.find_self_declared_shims(root / "TauCeti"), tracked)
        self.assertEqual(groups[0].declarations,
                         ("Complex.exists_bijOn_unitBall_map_eq_zero",))
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
            self.assertIn("test group", summary)

    def test_speculative_target_is_labeled(self):
        group = check.ShimGroup(
            (pathlib.Path("TauCeti/One.lean"),), ("Future.name",), (), "not named", True
        )
        available = check.available_replacements((group,), {"Future.name"}, pathlib.Path("."))
        summary = check.markdown_summary((group,), available)
        self.assertIn("Speculative target name", summary)

    def test_missing_mathlib_tree_rejects_module_checks(self):
        group = check.ShimGroup(
            (pathlib.Path("TauCeti/One.lean"),), (), ("Mathlib.Topology.NewThing",), "test"
        )
        with tempfile.TemporaryDirectory() as temporary:
            missing = pathlib.Path(temporary) / "missing"
            with self.assertRaisesRegex(RuntimeError, "Mathlib source tree does not exist"):
                check.available_replacements((group,), set(), missing)

    def test_zulip_report_is_idempotent_and_resolvable(self):
        summary = "## Expired Mathlib shim check\n\nFound replacements.\n"
        client = FakeZulip()
        check.reconcile_zulip(client, summary, active=True, channel="C", topic="T")
        self.assertEqual(len(client.sent), 1)
        self.assertEqual(client.narrows, [[['stream', 'C'], ['topic', 'T']]])

        active = client.sent[0]
        client = FakeZulip([{"id": 4, "sender_id": 7, "content": active}])
        check.reconcile_zulip(client, summary, active=True)
        self.assertEqual(client.sent, [])
        self.assertEqual(client.updated, [])

        clear = "## Expired Mathlib shim check\n\nNo replacements.\n"
        check.reconcile_zulip(client, clear, active=False)
        self.assertEqual(client.updated[0][0], 4)
        self.assertTrue(client.updated[0][1].startswith("✅"))

    def test_notification_report_round_trip(self):
        with tempfile.TemporaryDirectory() as temporary:
            report = pathlib.Path(temporary) / "report.json"
            report.write_text(
                json.dumps({"summary": "hello", "active": True}), encoding="utf-8"
            )
            self.assertEqual(check.load_notification_report(report), ("hello", True))


if __name__ == "__main__":
    unittest.main()
