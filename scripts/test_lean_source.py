#!/usr/bin/env python3
"""Regression tests for the reusable parser in ``scripts/lean_source.py``."""

from __future__ import annotations

import unittest

from lean_source import (
    declaration_returns_sort,
    declarations,
    include_commands,
    qualified_declarations,
    strip_comments_and_strings,
    variable_bindings,
)


class LeanSourceTests(unittest.TestCase):
    def test_primed_identifier_does_not_open_a_character_literal(self):
        cleaned = strip_comments_and_strings(
            "Homeomorph.prodAssoc F F' G' ''\ndef next := 1\n"
        )
        self.assertIn("def next", cleaned)

    def test_variable_bindings_retain_every_binder_kind(self):
        source = "variable (x : Nat) {y : Nat} ⦃z : Nat⦄ [i : Inhabited Nat]\n"
        [(position, bindings)] = variable_bindings(source)
        self.assertEqual(position, 0)
        self.assertEqual(
            [(binding.name, binding.kind) for binding in bindings],
            [("x", "explicit"), ("y", "implicit"), ("z", "strict-implicit"),
             ("i", "instance")],
        )

    def test_include_commands_and_sort_results_are_syntactic(self):
        self.assertEqual(
            [(action, names, one_shot) for _, action, names, one_shot in
             include_commands("include x y in\nomit z\n")],
            [("include", {"x", "y"}, True), ("omit", {"z"}, False)],
        )
        [declaration] = declarations("def Family (α : Type) : Nat → Type := fun _ => α\n")
        self.assertTrue(declaration_returns_sort(declaration))

    def test_qualified_declarations_applies_scopes_rooting_and_filter(self):
        source = """\
namespace Outer
def kept : Nat := 0
theorem skipped : True := True.intro
instance : Inhabited Nat := ⟨0⟩
def _root_.Rooted : Nat := 1
end Outer
"""
        self.assertEqual(
            qualified_declarations(source, keep=lambda declaration: declaration.keyword == "def"),
            {"Outer.kept", "Rooted"},
        )


if __name__ == "__main__":
    unittest.main()
