#!/usr/bin/env python3
"""Unit tests for the PR-status derivation (core) and the label sink (labels).

Pure logic only: the GitHub-reading helpers in core and the label writes in labels are stubbed, so
these run with no network and no `gh`. Run with:  python3 -m unittest test_pr_labels
"""

import os
import sys
import unittest
from unittest import mock

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


class RoadmapLabels(unittest.TestCase):
    def test_extracts_and_sorts_roadmaps_from_rest_objects(self):
        self.assertEqual(
            core._roadmap_labels([
                {"name": "awaiting-review"},
                {"name": "roadmap/Zeta"},
                {"name": "roadmap/Alpha"},
            ]),
            ["roadmap/Alpha", "roadmap/Zeta"],
        )

    def test_accepts_plain_names(self):
        self.assertEqual(
            core._roadmap_labels(["roadmap/PDE", "documentation"]),
            ["roadmap/PDE"],
        )

    def test_event_metadata_fast_path(self):
        env = {
            "PR_STATE": "open",
            "PR_HEAD": "abc",
            "PR_MERGED": "false",
            "PR_TITLE": "Title",
            "PR_AUTHOR": "alice",
            "PR_LABELS_JSON": '[{"name":"awaiting-CI"},{"name":"roadmap/PDE"}]',
        }
        with (
            mock.patch.dict(os.environ, env, clear=True),
            mock.patch.object(core, "gh_api", side_effect=AssertionError("must not fetch")),
        ):
            self.assertEqual(
                core.pr_state("9"),
                {
                    "state": "open",
                    "merged": False,
                    "head": "abc",
                    "title": "Title",
                    "author": "alice",
                    "roadmaps": ["roadmap/PDE"],
                    # The event payload carries no trustworthy mergeability, so the
                    # fast path reports "not known" and conflicting() resolves it.
                    "mergeable": None,
                },
            )

    def test_non_list_event_labels_degrade_to_empty(self):
        env = {"PR_STATE": "open", "PR_HEAD": "abc", "PR_LABELS_JSON": "null"}
        with mock.patch.dict(os.environ, env, clear=True):
            self.assertEqual(core.pr_state("9")["roadmaps"], [])


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


class Conflicting(unittest.TestCase):
    """core.conflicting maps GitHub's tri-state `mergeable` onto True/False/None."""

    def setUp(self):
        self._saved = core.gh_api
        self.calls = []

    def tearDown(self):
        core.gh_api = self._saved

    def answer(self, *values):
        replies = list(values)
        def fake(path, jq=None, paginate=False):
            self.calls.append(path)
            return replies.pop(0)
        core.gh_api = fake

    def test_prefetched_state_costs_no_request(self):
        core.gh_api = lambda *a, **k: self.fail("must not fetch")
        self.assertIs(core.conflicting("1", {"mergeable": False}), True)
        self.assertIs(core.conflicting("1", {"mergeable": True}), False)

    def test_reads_when_the_state_has_no_answer(self):
        self.answer("false\n")
        self.assertIs(core.conflicting("1", {"mergeable": None}), True)
        self.assertEqual(len(self.calls), 1)

    def test_polls_through_a_not_yet_computed_answer(self):
        self.answer("null\n", "true\n")
        self.assertIs(core.conflicting("1", None, sleep=lambda s: None), False)
        self.assertEqual(len(self.calls), 2)

    def test_gives_up_as_unknown_never_as_mergeable(self):
        self.answer(*(["null\n"] * core.MERGEABLE_POLLS))
        self.assertIsNone(core.conflicting("1", None, sleep=lambda s: None))
        self.assertEqual(len(self.calls), core.MERGEABLE_POLLS)


class RateLimitBackoff(unittest.TestCase):
    """gh does not retry a rate limit; every sink here shares one App budget."""

    def run_with(self, *results):
        replies = list(results)
        class Result:
            def __init__(self, rc, err): self.returncode, self.stderr, self.stdout = rc, err, "ok"
        with mock.patch.object(core.subprocess, "run",
                               side_effect=[Result(*r) for r in replies]) as run:
            return core.gh_api("/x", sleep=lambda s: None), run.call_count

    def test_retries_through_a_rate_limit(self):
        out, calls = self.run_with((1, "API rate limit exceeded"), (0, ""))
        self.assertEqual((out, calls), ("ok", 2))

    def test_a_normal_failure_is_not_retried(self):
        with mock.patch.object(core.subprocess, "run") as run:
            run.return_value = mock.Mock(returncode=1, stderr="404 Not Found", stdout="")
            with self.assertRaises(RuntimeError):
                core.gh_api("/x", sleep=lambda s: None)
            self.assertEqual(run.call_count, 1)

    def test_a_persistent_rate_limit_eventually_raises(self):
        with mock.patch.object(core.subprocess, "run") as run:
            run.return_value = mock.Mock(returncode=1, stderr="secondary rate limit", stdout="")
            with self.assertRaises(RuntimeError):
                core.gh_api("/x", sleep=lambda s: None)
            self.assertEqual(run.call_count, core.RATE_LIMIT_RETRIES)

    def test_a_write_goes_through_the_same_back_off(self):
        # conflicts.py posts its notice through gh_api, so the sweep's writes share
        # the budget protection its reads have. Retrying is safe: a rate-limited call
        # was refused, so it cannot double-post the comment it was carrying.
        results = [mock.Mock(returncode=1, stderr="API rate limit exceeded", stdout=""),
                   mock.Mock(returncode=0, stderr="", stdout="ok")]
        with mock.patch.object(core.subprocess, "run", side_effect=results) as run:
            core.gh_api("/x", method="POST", fields={"body": "b"}, sleep=lambda s: None)
        self.assertEqual(run.call_count, 2)
        self.assertEqual(run.call_args.args[0],
                         ["gh", "api", "/x", "--method", "POST", "-f", "body=b"])

    def test_retry_transient_is_opt_in(self):
        # The bulk chart reads ride out a 502; a status sink must not, or a sweep
        # papers over a read it should have failed and left for the next run.
        for retry_transient, expected in ((False, 1), (True, core.RATE_LIMIT_RETRIES)):
            with mock.patch.object(core.subprocess, "run") as run:
                run.return_value = mock.Mock(returncode=1, stderr="HTTP 502", stdout="")
                with self.assertRaises(RuntimeError):
                    core.run_gh(["api", "/x"], "gh api /x", sleep=lambda s: None,
                                retry_transient=retry_transient)
                self.assertEqual(run.call_count, expected, retry_transient)


class DerivedLabel(unittest.TestCase):
    def label(self, lifecycle="open", ci=None, review="none", inprogress=False,
              conflicting=False):
        return labels.derived_label(
            {"lifecycle": lifecycle, "ci": ci, "review": review, "conflicting": conflicting,
             "review_inprogress": inprogress, "head": "h", "title": "t"})

    def test_conflict_outranks_every_open_state(self):
        for ci in (None, "running", "success", "failure"):
            for review in ("none", "running", "changes", "approved"):
                self.assertEqual(
                    self.label(ci=ci, review=review, conflicting=True), "merge-conflict",
                    f"ci={ci} review={review}")

    def test_conflict_never_survives_a_terminal_pr(self):
        self.assertIsNone(self.label(lifecycle="merged", conflicting=True))
        self.assertIsNone(self.label(lifecycle="closed", conflicting=True))

    def test_unknown_mergeability_does_not_paint_a_conflict(self):
        # None means "GitHub has not computed it", not "no conflict"; a state we
        # have not established must never displace the one we can see.
        self.assertEqual(self.label(ci="success", review="approved", conflicting=None),
                         "ready-to-merge")
        self.assertEqual(self.label(ci="running", conflicting=None), "awaiting-CI")

    def test_absent_conflict_key_is_tolerated(self):
        # A caller with an older status dict must still get a label, not a KeyError.
        self.assertEqual(
            labels.derived_label({"lifecycle": "open", "ci": "success", "review": "approved",
                                  "review_inprogress": False, "head": "h", "title": "t"}),
            "ready-to-merge")

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
        self._saved = (core.pr_state, core.ci_status, core.trusted_comments, core.conflicting)

    def tearDown(self):
        (core.pr_state, core.ci_status, core.trusted_comments,
         core.conflicting) = self._saved

    def stub(self, state="open", merged=False, ci="success", comments=None, conflict=False):
        core.pr_state = lambda pr: {"state": state, "merged": merged, "head": "H", "title": "T",
                                    "mergeable": None}
        core.ci_status = lambda head: ci
        core.trusted_comments = lambda pr: (comments or [])
        core.conflicting = lambda pr, st=None: conflict

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
        self.assertIsNone(d["conflicting"])
        self.assertFalse(d["review_inprogress"])

    def test_state_param_avoids_refetch(self):
        called = {"n": 0}

        def boom(pr):
            called["n"] += 1
            raise AssertionError("pr_state should not be called when state= is passed")

        core.pr_state = boom
        core.ci_status = lambda head: "running"
        core.trusted_comments = lambda pr: []
        core.conflicting = lambda pr, st=None: False
        d = core.derive("1", state={"state": "open", "merged": False, "head": "H", "title": "T",
                                    "mergeable": True})
        self.assertEqual(d["ci"], "running")
        self.assertEqual(called["n"], 0)

    def test_ci_override_none_maps_to_none(self):
        self.stub(ci="success")
        self.assertIsNone(core.derive("1", ci_override="none")["ci"])

    def test_conflict_override_replaces_the_read(self):
        # The sweep already knows every PR's mergeability, so passing it must skip
        # the per-PR read entirely rather than merely agreeing with it.
        self.stub()
        core.conflicting = lambda pr, st=None: self.fail("must not re-read mergeability")
        self.assertIs(core.derive("1", conflict_override=True)["conflicting"], True)

    def test_conflict_is_read_when_not_overridden(self):
        self.stub(conflict=True)
        self.assertIs(core.derive("1")["conflicting"], True)


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
        self.overrides = []

        def derive(pr, ci=None, conflict_override=None, **kwargs):
            self.overrides.append(conflict_override)
            return status

        labels.core.derive = derive
        labels.current_status_labels = lambda pr: present

    def status(self, **kwargs):
        base = {"lifecycle": "open", "ci": "success", "review": "approved",
                "conflicting": False, "review_inprogress": False, "head": "h", "title": "t"}
        base.update(kwargs)
        return base

    def test_switches_to_the_single_desired_label(self):
        self.run_with(self.status(), present=["awaiting-review"])
        labels.reconcile("1")
        self.assertEqual(self.added, ["ready-to-merge"])
        self.assertEqual(self.removed, ["awaiting-review"])

    def test_idempotent_when_already_correct(self):
        self.run_with(self.status(ci=None, review="none"), present=["awaiting-CI"])
        labels.reconcile("1")
        self.assertEqual(self.added, [])
        self.assertEqual(self.removed, [])

    def test_terminal_strips_all(self):
        self.run_with(self.status(lifecycle="merged", ci=None, review=None),
                      present=["ready-to-merge", "review-in-progress"])
        labels.reconcile("1")
        self.assertEqual(self.added, [])
        self.assertEqual(sorted(self.removed), ["ready-to-merge", "review-in-progress"])

    def test_conflict_replaces_whatever_label_was_there(self):
        self.run_with(self.status(conflicting=True), present=["ready-to-merge"])
        labels.reconcile("1")
        self.assertEqual(self.added, ["merge-conflict"])
        self.assertEqual(self.removed, ["ready-to-merge"])

    def test_resolved_conflict_gives_the_label_back(self):
        self.run_with(self.status(), present=["merge-conflict"])
        labels.reconcile("1")
        self.assertEqual(self.added, ["ready-to-merge"])
        self.assertEqual(self.removed, ["merge-conflict"])

    def test_uncomputed_mergeability_keeps_an_established_conflict(self):
        # GitHub answers null for a while after every push, which is exactly when a
        # PR event fires this. Deriving from None would strip the label off a
        # still-conflicting PR until the hourly sweep put it back.
        self.run_with(self.status(conflicting=None), present=["merge-conflict"])
        labels.reconcile("1")
        self.assertEqual((self.added, self.removed), ([], []))

    def test_uncomputed_mergeability_does_not_invent_a_conflict(self):
        self.run_with(self.status(conflicting=None), present=["awaiting-review"])
        labels.reconcile("1")
        self.assertEqual(self.added, ["ready-to-merge"])
        self.assertEqual(self.removed, ["awaiting-review"])

    def test_only_a_positive_answer_clears_the_conflict_label(self):
        self.run_with(self.status(conflicting=False), present=["merge-conflict"])
        labels.reconcile("1")
        self.assertEqual(self.added, ["ready-to-merge"])
        self.assertEqual(self.removed, ["merge-conflict"])

    def test_a_terminal_pr_still_strips_a_kept_conflict_label(self):
        self.run_with(self.status(lifecycle="merged", ci=None, review=None, conflicting=None),
                      present=["merge-conflict"])
        labels.reconcile("1")
        self.assertEqual((self.added, self.removed), ([], ["merge-conflict"]))

    def test_conflict_override_is_plumbed_through(self):
        self.run_with(self.status(conflicting=True), present=[])
        labels.reconcile("1", conflict_override=True)
        self.assertEqual(self.overrides, [True])


if __name__ == "__main__":
    unittest.main()
