#!/usr/bin/env python3
"""Unit tests for the PR-status derivation (core) and the label sink (labels).

Pure logic only: the GitHub-reading helpers in core and the label writes in labels are stubbed, so
these run with no network and no `gh`. Run with:  python3 -m unittest test_pr_labels
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core  # noqa: E402
import labels  # noqa: E402


class ReviewState(unittest.TestCase):
    HEAD = "abc123"

    def rs(self, meta):
        return core.review_state(meta, self.HEAD)

    def test_no_scoreboard_is_none(self):
        self.assertEqual(self.rs({}), "none")

    def test_behind_head_is_running(self):
        self.assertEqual(self.rs({"head_sha": "old", "states": {"naming": "green"}}), "running")

    # --- authoritative `states` map (the durable per-rubric signal) ---
    def test_states_all_green_is_approved(self):
        self.assertEqual(self.rs({"head_sha": self.HEAD, "states": {"a": "green", "b": "green"}}), "approved")

    def test_states_any_blocking_is_changes(self):
        self.assertEqual(
            self.rs({"head_sha": self.HEAD, "states": {"a": "green", "b": "blocking_request"}}), "changes")

    def test_states_beats_a_greener_latest_round(self):
        # The bug the fix targets: latest `runs` approves one rubric while another still blocks in states.
        meta = {"head_sha": self.HEAD,
                "runs": [{"rubric": "naming", "verdict": "approve"}],
                "states": {"naming": "green", "documentation": "blocking_request"}}
        self.assertEqual(self.rs(meta), "changes")

    def test_states_stale_carried_is_not_yet_approved(self):
        self.assertEqual(self.rs({"head_sha": self.HEAD, "states": {"a": "green", "b": "stale"}}), "running")

    # --- legacy fallback to `runs` when no states map ---
    def test_runs_fallback_all_approve(self):
        self.assertEqual(self.rs({"head_sha": self.HEAD, "runs": [{"verdict": "approve"}]}), "approved")

    def test_runs_fallback_blocking(self):
        self.assertEqual(
            self.rs({"head_sha": self.HEAD, "runs": [{"verdict": "approve"}, {"verdict": "request_changes"}]}),
            "changes")

    def test_runs_fallback_empty_is_running(self):
        self.assertEqual(self.rs({"head_sha": self.HEAD, "runs": []}), "running")


class ScoreboardMeta(unittest.TestCase):
    def test_parses_meta_with_nested_states(self):
        # Regression: a lazy `\{.*?\}` truncated at the first inner `}` and dropped the whole meta.
        body = ('<!--tauceti-scoreboard-->\n'
                '<!--tauceti-meta:v1 {"head_sha":"H","states":{"correctness":"blocking_block",'
                '"reuse":"green"},"full_rounds":2}--> trailing text')
        meta = core.scoreboard_meta_from([{"body": body, "updated": "2026-01-01"}])
        self.assertEqual(meta.get("states", {}).get("correctness"), "blocking_block")
        self.assertEqual(meta.get("full_rounds"), 2)

    def test_newest_trusted_comment_wins(self):
        old = {"body": '<!--tauceti-scoreboard--><!--tauceti-meta:v1 {"n":1}-->', "updated": "2026-01-01"}
        new = {"body": '<!--tauceti-scoreboard--><!--tauceti-meta:v1 {"n":2}-->', "updated": "2026-02-01"}
        self.assertEqual(core.scoreboard_meta_from([old, new]).get("n"), 2)

    def test_no_marker_is_empty(self):
        self.assertEqual(core.scoreboard_meta_from([{"body": "hi", "updated": "x"}]), {})


class InProgress(unittest.TestCase):
    HEAD = "H" * 40
    NOW = 1_700_000_000

    def marker(self, head, expires):
        return {"body": '<!--tauceti-review-in-progress {"head": "%s", "expires_at": %d}-->' % (head, expires)}

    def test_unexpired_at_head_is_true(self):
        self.assertTrue(core.inprogress_from([self.marker(self.HEAD, self.NOW + 900)], self.HEAD, self.NOW))

    def test_expired_is_false(self):
        self.assertFalse(core.inprogress_from([self.marker(self.HEAD, self.NOW - 1)], self.HEAD, self.NOW))

    def test_wrong_head_is_false(self):
        self.assertFalse(core.inprogress_from([self.marker("O" * 40, self.NOW + 900)], self.HEAD, self.NOW))

    def test_malformed_is_ignored(self):
        self.assertFalse(core.inprogress_from([{"body": "<!--tauceti-review-in-progress {bad-->"}], self.HEAD, self.NOW))

    def test_no_marker_is_false(self):
        self.assertFalse(core.inprogress_from([{"body": "just a comment"}], self.HEAD, self.NOW))


class DerivedLabel(unittest.TestCase):
    def label(self, lifecycle="open", ci=None, review="none", inprogress=False):
        return labels.derived_label(
            {"lifecycle": lifecycle, "ci": ci, "review": review,
             "review_inprogress": inprogress, "head": "h", "title": "t"})

    def test_merged_and_closed_have_no_label(self):
        self.assertIsNone(self.label(lifecycle="merged"))
        self.assertIsNone(self.label(lifecycle="closed"))

    def test_ci_not_reported_or_running_is_awaiting_ci(self):
        self.assertEqual(self.label(ci=None), "awaiting-CI")
        self.assertEqual(self.label(ci="running"), "awaiting-CI")

    def test_ci_failure_is_awaiting_author(self):
        self.assertEqual(self.label(ci="failure"), "awaiting-author")

    def test_green_changes_is_awaiting_author(self):
        self.assertEqual(self.label(ci="success", review="changes"), "awaiting-author")

    def test_green_approved_is_ready(self):
        self.assertEqual(self.label(ci="success", review="approved"), "ready-to-merge")

    def test_green_pending_no_marker_is_awaiting_review(self):
        self.assertEqual(self.label(ci="success", review="none"), "awaiting-review")
        self.assertEqual(self.label(ci="success", review="running"), "awaiting-review")

    def test_green_pending_with_marker_is_review_in_progress(self):
        self.assertEqual(self.label(ci="success", review="none", inprogress=True), "review-in-progress")
        self.assertEqual(self.label(ci="success", review="running", inprogress=True), "review-in-progress")

    def test_marker_only_overlays_the_awaiting_review_slot(self):
        # A live marker never overrides a more important state.
        self.assertEqual(self.label(ci="running", inprogress=True), "awaiting-CI")
        self.assertEqual(self.label(ci="failure", inprogress=True), "awaiting-author")
        self.assertEqual(self.label(ci="success", review="changes", inprogress=True), "awaiting-author")
        self.assertEqual(self.label(ci="success", review="approved", inprogress=True), "ready-to-merge")


class Derive(unittest.TestCase):
    """core.derive glues pr_state/ci_status/trusted_comments together; stub them."""

    def setUp(self):
        self._saved = (core.pr_state, core.ci_status, core.trusted_comments)

    def tearDown(self):
        core.pr_state, core.ci_status, core.trusted_comments = self._saved

    def stub(self, state="open", merged=False, ci="success", comments=None):
        core.pr_state = lambda pr: {"state": state, "merged": merged, "head": "H", "title": "T"}
        core.ci_status = lambda head: ci
        core.trusted_comments = lambda pr: (comments or [])

    def test_open_plumbs_inprogress(self):
        self.stub(ci="success",
                  comments=[{"body": '<!--tauceti-review-in-progress {"head": "H", "expires_at": 9999999999}-->'}])
        d = core.derive("1", now=1_700_000_000)
        self.assertEqual(d["lifecycle"], "open")
        self.assertTrue(d["review_inprogress"])

    def test_terminal_clears_everything(self):
        self.stub(state="closed", merged=True, ci="success",
                  comments=[{"body": '<!--tauceti-review-in-progress {"head": "H", "expires_at": 9999999999}-->'}])
        d = core.derive("1")
        self.assertEqual(d["lifecycle"], "merged")
        self.assertIsNone(d["ci"])
        self.assertIsNone(d["review"])
        self.assertFalse(d["review_inprogress"])

    def test_state_param_avoids_refetch(self):
        called = {"n": 0}

        def boom(pr):
            called["n"] += 1
            raise AssertionError("pr_state should not be called when state= is passed")

        core.pr_state = boom
        core.ci_status = lambda head: "running"
        core.trusted_comments = lambda pr: []
        d = core.derive("1", state={"state": "open", "merged": False, "head": "H", "title": "T"})
        self.assertEqual(d["ci"], "running")
        self.assertEqual(called["n"], 0)

    def test_ci_override_none_maps_to_none(self):
        self.stub(ci="success")
        self.assertIsNone(core.derive("1", ci_override="none")["ci"])


class Reconcile(unittest.TestCase):
    """labels.reconcile drives the label set to exactly {desired}; stub derive and the writes."""

    def setUp(self):
        self._d = labels.core.derive
        self._c = labels.current_status_labels
        self._a = labels.add_label
        self._r = labels.remove_label
        self.added, self.removed = [], []
        labels.add_label = lambda pr, name: self.added.append(name)
        labels.remove_label = lambda pr, name: self.removed.append(name)

    def tearDown(self):
        labels.core.derive = self._d
        labels.current_status_labels = self._c
        labels.add_label = self._a
        labels.remove_label = self._r

    def run_with(self, status, present):
        labels.core.derive = lambda pr, ci=None: status
        labels.current_status_labels = lambda pr: present

    def test_switches_to_the_single_desired_label(self):
        self.run_with(
            {"lifecycle": "open", "ci": "success", "review": "approved", "review_inprogress": False,
             "head": "h", "title": "t"},
            present=["awaiting-review"])
        labels.reconcile("1")
        self.assertEqual(self.added, ["ready-to-merge"])
        self.assertEqual(self.removed, ["awaiting-review"])

    def test_idempotent_when_already_correct(self):
        self.run_with(
            {"lifecycle": "open", "ci": None, "review": "none", "review_inprogress": False,
             "head": "h", "title": "t"},
            present=["awaiting-CI"])
        labels.reconcile("1")
        self.assertEqual(self.added, [])
        self.assertEqual(self.removed, [])

    def test_terminal_strips_all(self):
        self.run_with(
            {"lifecycle": "merged", "ci": None, "review": None, "review_inprogress": False,
             "head": "h", "title": "t"},
            present=["ready-to-merge", "review-in-progress"])
        labels.reconcile("1")
        self.assertEqual(self.added, [])
        self.assertEqual(sorted(self.removed), ["ready-to-merge", "review-in-progress"])


if __name__ == "__main__":
    unittest.main()
