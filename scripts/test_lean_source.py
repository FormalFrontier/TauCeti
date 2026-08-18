#!/usr/bin/env python3
"""Regression tests for the reusable parser in ``scripts/lean_source.py``."""

from __future__ import annotations

import unittest

from lean_source import qualified_declarations


class LeanSourceTests(unittest.TestCase):
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
