#!/usr/bin/env python3
"""Unit tests for the merge-conflict label sweep.

Pure logic only: every `gh` call is stubbed, so these run with no network and no
`gh`. Run with:  python3 test_conflicts.py
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import conflicts  # noqa: E402


def pr(number, conflicting, labels=None, base="main"):
    return {"number": number, "conflicting": conflicting, "base": base,
            "labels": labels or []}


class Reconcile(unittest.TestCase):
    """The label is the state, so reconcile is a two-way convergence."""

    def setUp(self):
        self.calls = []
        self._gh = conflicts._gh
        conflicts._gh = lambda args: self.calls.append(args) or ""
        self.addCleanup(setattr, conflicts, "_gh", self._gh)

    def kinds(self):
        """['comment'|'label'|'unlabel', ...] in the order they were issued."""
        out = []
        for args in self.calls:
            path = next((a for a in args if a.startswith("/repos/")), "")
            if "/comments" in path:
                out.append("comment")
            elif "DELETE" in args:
                out.append("unlabel")
            elif "/labels" in path:
                out.append("label")
        return out

    def test_a_new_conflict_is_commented_then_labelled(self):
        # Order matters: the label suppresses a repeat, so it must be written LAST
        # or a comment that fails is never retried.
        self.assertEqual(conflicts.reconcile(pr(7, True)), "labelled")
        self.assertEqual(self.kinds(), ["comment", "label"])

    def test_the_comment_names_the_prs_own_base(self):
        conflicts.reconcile(pr(7, True, base="release/v2"))
        body = [a for a in self.calls
                if any("/comments" in part for part in a)][0][-1]
        self.assertIn("release/v2", body)
        self.assertNotIn("`main`", body)

    def test_an_already_labelled_conflict_is_left_alone(self):
        self.assertEqual(conflicts.reconcile(pr(7, True, [conflicts.LABEL])), "unchanged")
        self.assertEqual(self.calls, [])

    def test_merging_again_removes_the_label(self):
        self.assertEqual(conflicts.reconcile(pr(7, False, [conflicts.LABEL])), "cleared")
        self.assertEqual(self.kinds(), ["unlabel"])

    def test_a_clean_unlabelled_pr_does_nothing(self):
        self.assertEqual(conflicts.reconcile(pr(7, False)), "unchanged")
        self.assertEqual(self.calls, [])

    def test_unknown_mergeability_changes_nothing_either_way(self):
        self.assertEqual(conflicts.reconcile(pr(7, None)), "skipped")
        self.assertEqual(conflicts.reconcile(pr(8, None, [conflicts.LABEL])), "skipped")
        self.assertEqual(self.calls, [])

    def test_a_parked_pr_is_left_entirely_alone(self):
        # Not labelled-but-silent: the label means "we told the author", so
        # labelling without commenting would leave the conflict permanently silent
        # once the hold came off, the label having already claimed it was handled.
        self.assertEqual(conflicts.reconcile(pr(7, True, ["keep"])), "parked")
        self.assertEqual(self.calls, [])

    def test_unparking_a_conflicting_pr_then_announces_it(self):
        self.assertEqual(conflicts.reconcile(pr(7, True, ["hold"])), "parked")
        self.assertEqual(conflicts.reconcile(pr(7, True)), "labelled")
        self.assertEqual(self.kinds(), ["comment", "label"])

    def test_dry_run_decides_but_writes_nothing(self):
        self.assertEqual(conflicts.reconcile(pr(7, True), dry_run=True), "labelled")
        self.assertEqual(self.calls, [])


class Unknowns(unittest.TestCase):
    """UNKNOWN must cost the PR it affects, never the rest of the run."""

    def setUp(self):
        self._open = conflicts.open_prs
        self.addCleanup(setattr, conflicts, "open_prs", self._open)

    def test_a_later_round_fills_in_what_the_first_could_not(self):
        rows = [pr(1, None), pr(2, False)]
        conflicts.open_prs = lambda: [pr(1, True), pr(2, False)]
        conflicts.resolve_unknowns(rows, sleep=lambda s: None)
        self.assertEqual([r["conflicting"] for r in rows], [True, False])

    def test_a_permanently_unknown_pr_stays_unknown(self):
        rows = [pr(1, None)]
        conflicts.open_prs = lambda: [pr(1, None)]
        conflicts.resolve_unknowns(rows, sleep=lambda s: None)
        self.assertIsNone(rows[0]["conflicting"])

    def test_a_failed_re_read_keeps_what_is_already_known(self):
        def boom():
            raise RuntimeError("GitHub is down")
        rows = [pr(1, None), pr(2, True)]
        conflicts.open_prs = boom
        conflicts.resolve_unknowns(rows, sleep=lambda s: None)
        self.assertEqual([r["conflicting"] for r in rows], [None, True])

    def test_a_resolved_row_is_replaced_wholesale(self):
        # Pairing fresh mergeability with stale labels is how a PR gets commented
        # on twice.
        rows = [pr(1, None, labels=[])]
        conflicts.open_prs = lambda: [pr(1, True, labels=[conflicts.LABEL])]
        conflicts.resolve_unknowns(rows, sleep=lambda s: None)
        self.assertEqual(rows[0]["labels"], [conflicts.LABEL])

    def test_no_unknowns_costs_no_extra_query(self):
        conflicts.open_prs = lambda: self.fail("must not re-read when nothing is unknown")
        conflicts.resolve_unknowns([pr(1, False)], sleep=lambda s: None)


class EnsureLabel(unittest.TestCase):
    """The label is the episode state, so a missing one must stop the sweep."""

    def setUp(self):
        self._run = conflicts.subprocess.run
        self.addCleanup(setattr, conflicts.subprocess, "run", self._run)

    def results(self, *pairs):
        seq = [type("R", (), {"returncode": c, "stderr": e, "stdout": ""})()
               for c, e in pairs]
        conflicts.subprocess.run = lambda *a, **k: seq.pop(0)

    def test_an_existing_label_needs_no_create(self):
        self.results((0, ""))
        conflicts.ensure_label()

    def test_a_missing_label_is_created(self):
        self.results((1, "gh: Not Found (HTTP 404)"), (0, ""))
        conflicts.ensure_label()

    def test_a_concurrent_create_is_fine(self):
        self.results((1, "404"), (1, "already_exists"))
        conflicts.ensure_label()

    def test_an_unconfirmable_label_raises_rather_than_proceeding(self):
        # The finding: silently returning here let the sweep comment on every
        # conflicting PR while every label write failed, so the next run commented
        # on them all again.
        self.results((1, "gh: Bad gateway (HTTP 502)"), (1, "gh: Bad gateway (HTTP 502)"))
        with self.assertRaises(RuntimeError):
            conflicts.ensure_label()


class Sweep(unittest.TestCase):
    def setUp(self):
        self._open, self._reconcile = conflicts.open_prs, conflicts.reconcile
        self._ensure = conflicts.ensure_label
        self.seen = []
        conflicts.ensure_label = lambda: None
        conflicts.reconcile = lambda p, dry_run=False: self.seen.append(p["number"])
        self.addCleanup(setattr, conflicts, "open_prs", self._open)
        self.addCleanup(setattr, conflicts, "reconcile", self._reconcile)
        self.addCleanup(setattr, conflicts, "ensure_label", self._ensure)

    def test_an_unknown_pr_does_not_starve_the_others(self):
        # The whole reason this is not the upstream action: there, one permanently
        # unknown PR abandons the page and everything after it.
        conflicts.open_prs = lambda: [pr(1, None), pr(2, True), pr(3, True)]
        self.assertEqual(conflicts.sweep(sleep=lambda s: None), 0)
        self.assertEqual(self.seen, [2, 3])

    def test_one_failing_pr_does_not_stop_the_rest(self):
        def boom(p, dry_run=False):
            if p["number"] == 1:
                raise RuntimeError("GitHub said no")
            self.seen.append(p["number"])
        conflicts.open_prs = lambda: [pr(1, True), pr(2, True)]
        conflicts.reconcile = boom
        self.assertEqual(conflicts.sweep(sleep=lambda s: None), 1)
        self.assertEqual(self.seen, [2])

    def test_the_label_is_provisioned_only_when_something_needs_it(self):
        created = []
        conflicts.ensure_label = lambda: created.append(True)
        conflicts.open_prs = lambda: [pr(1, False), pr(2, False)]
        conflicts.sweep(sleep=lambda s: None)
        self.assertEqual(created, [])
        conflicts.open_prs = lambda: [pr(1, True)]
        conflicts.sweep(sleep=lambda s: None)
        self.assertEqual(created, [True])

    def test_dry_run_provisions_nothing(self):
        created = []
        conflicts.ensure_label = lambda: created.append(True)
        conflicts.open_prs = lambda: [pr(1, True)]
        conflicts.sweep(dry_run=True, sleep=lambda s: None)
        self.assertEqual(created, [])


if __name__ == "__main__":
    unittest.main()
