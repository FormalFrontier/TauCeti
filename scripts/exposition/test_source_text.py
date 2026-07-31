#!/usr/bin/env python3
"""Tests for statement slicing from Lean sources.

Run with:

    python3 scripts/exposition/test_source_text.py
"""

import unittest

from source_text import SourceFile, code_view, statement_slice


def slice_text(text: str, fallback: str = "theorem"):
    """Slice a single-declaration source; the declaration spans the text."""
    source = SourceFile.from_text(text)
    lines = text.split("\n")
    declaration_range = [1, 0, len(lines), len(lines[-1])]
    # Selection: line/col of the token after the first keyword occurrence —
    # tests pass it explicitly when it matters; default to start of text.
    return statement_slice(source, declaration_range, [1, 0], fallback)


class CodeViewTest(unittest.TestCase):
    def test_blanks_line_comments_preserving_length(self):
        text = "foo -- bar\nbaz"
        view = code_view(text)
        self.assertEqual(len(view), len(text))
        self.assertNotIn("bar", view)
        self.assertIn("foo", view)
        self.assertIn("baz", view)

    def test_blanks_nested_block_comments(self):
        text = "a /- x /- y -/ z -/ b"
        view = code_view(text)
        self.assertNotIn("x", view)
        self.assertNotIn("y", view)
        self.assertNotIn("z", view)
        self.assertIn("a", view)
        self.assertIn("b", view)

    def test_newlines_survive_in_comments_and_strings(self):
        text = '/- a\nb -/ "s\nt"'
        view = code_view(text)
        self.assertEqual(view.count("\n"), 2)


class StatementSliceTest(unittest.TestCase):
    def test_theorem_statement_stops_at_assign(self):
        kind, statement = slice_text("theorem foo : 1 = 1 := rfl")
        self.assertEqual(kind, "theorem")
        self.assertEqual(statement, "theorem foo : 1 = 1")

    def test_lemma_keyword_refines_coarse_kind(self):
        kind, statement = slice_text("lemma bar (n : Nat) : n = n := rfl")
        self.assertEqual(kind, "lemma")
        self.assertEqual(statement, "lemma bar (n : Nat) : n = n")

    def test_instance_keyword_refines_def(self):
        kind, _ = slice_text("instance : Inhabited Nat := ⟨0⟩", fallback="def")
        self.assertEqual(kind, "instance")

    def test_modifiers_and_attributes_are_skipped(self):
        kind, statement = slice_text(
            "@[simp]\nprivate noncomputable def q : Nat := 0", fallback="def"
        )
        self.assertEqual(kind, "def")
        self.assertTrue(statement.startswith("def q"))

    def test_module_system_public_modifier_is_skipped(self):
        kind, statement = slice_text("public theorem t : True := trivial")
        self.assertEqual(kind, "theorem")
        self.assertTrue(statement.startswith("theorem t"))

    def test_where_ends_the_statement(self):
        kind, statement = slice_text(
            "def s : Nat where\n  x := 1", fallback="def"
        )
        self.assertEqual(statement, "def s : Nat")

    def test_inductive_bars_end_the_statement(self):
        _, statement = slice_text(
            "inductive Color\n| red\n| green", fallback="inductive"
        )
        self.assertEqual(statement, "inductive Color")

    def test_let_in_type_keeps_its_assign(self):
        _, statement = slice_text(
            "theorem t : let n := 3\nn = 3 := rfl"
        )
        self.assertEqual(statement, "theorem t : let n := 3\nn = 3")

    def test_alias_keeps_fallback_kind_and_alias_text(self):
        kind, statement = slice_text(
            "@[deprecated foo (since := \"2026-01-01\")]\nalias old := foo"
        )
        self.assertEqual(kind, "theorem")
        self.assertTrue(statement.startswith("alias old"))

    def test_generated_mid_line_range_yields_empty_statement(self):
        # `to_additive`-style declarations point their range at a mid-line
        # token; the slice must bail out instead of emitting a fragment.
        text = "theorem mul_thing : True := trivial"
        source = SourceFile.from_text(text)
        kind, statement = statement_slice(source, [1, 8, 1, 17], [1, 8], "theorem")
        self.assertEqual(kind, "theorem")
        self.assertEqual(statement, "")

    def test_statement_is_capped(self):
        text = "theorem long : " + "Nat → " * 500 + "Nat := fun n => n"
        _, statement = slice_text(text)
        self.assertLessEqual(len(statement), 1200)
        self.assertTrue(statement.endswith("…"))

    def test_doc_comment_before_keyword_is_ignored(self):
        _, statement = slice_text(
            "/-- A doc with := inside. -/\ntheorem d : True := trivial"
        )
        self.assertEqual(statement, "theorem d : True")


if __name__ == "__main__":
    unittest.main()
