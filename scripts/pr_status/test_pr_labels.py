#!/usr/bin/env python3
"""Unit tests for the PR-status derivation (core) and the label sink (labels).

Pure logic only: the GitHub-reading helpers in core and the label writes in labels are stubbed, so
these run with no network and no `gh`. Run with:  python3 -m unittest test_pr_labels
"""

import json
import os
import sys
import unittest
from types import SimpleNamespace
from unittest import mock

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core  # noqa: E402
import labels  # noqa: E402


# Real `gh api` stderr: the API message, then the status gh appends.
SECONDARY_403 = ("gh: You have exceeded a secondary rate limit and have been "
                 "temporarily blocked from content creation. (HTTP 403)")
ABUSE_403 = ("gh: You have triggered an abuse detection mechanism. "
             "Please wait a few minutes before you try again. (HTTP 403)")
PRIMARY_403 = "gh: API rate limit exceeded for installation. (HTTP 403)"
TOO_MANY_429 = "gh: Too Many Requests (HTTP 429)"
NOT_FOUND_404 = "gh: Not Found (HTTP 404)"
# The finding this pins: wording alone must not trigger a retry.
NOT_FOUND_MENTIONING_RATE = ("gh: No workflow named 'rate limit dashboard' "
                             "was found. (HTTP 404)")


class RateLimitClassification(unittest.TestCase):
    """Status first, wording second: `gh` reports rate limits as 403 or 429."""

    def test_recognises_the_real_limit_responses(self):
        for stderr in (SECONDARY_403, ABUSE_403, PRIMARY_403, TOO_MANY_429):
            with self.subTest(stderr=stderr[:40]):
                self.assertTrue(core._rate_limited(stderr))

    def test_a_404_is_never_a_rate_limit_however_it_is_worded(self):
        self.assertFalse(core._rate_limited(NOT_FOUND_404))
        self.assertFalse(core._rate_limited(NOT_FOUND_MENTIONING_RATE))

    def test_a_403_that_is_merely_forbidden_is_not_retried(self):
        self.assertFalse(core._rate_limited("gh: Resource not accessible by "
                                            "integration (HTTP 403)"))

    def test_stderr_with_no_status_is_not_retried(self):
        self.assertFalse(core._rate_limited("gh: connection reset"))


class RateLimitBackoff(unittest.TestCase):
    """`gh` does not retry a rate limit, and a burst can spend the budget."""

    def setUp(self):
        core._BLOCKED_UNTIL = 0.0
        self.addCleanup(setattr, core, "_BLOCKED_UNTIL", 0.0)

    def result(self, code, err):
        return mock.Mock(returncode=code, stderr=err, stdout="ok")

    def call(self, results, quota=None, waits=None):
        """Run gh_api over canned subprocess results. `quota` is what the quota
        probe reports: None = secondary limit, an int = seconds to reset."""
        record = waits.append if waits is not None else (lambda s: None)
        state = ((core.QUOTA_EXHAUSTED, quota) if isinstance(quota, int)
                 else (quota or core.QUOTA_OK, None))
        with (mock.patch.object(core.subprocess, "run") as run,
              mock.patch.object(core.time, "sleep", record),
              mock.patch.object(core, "_quota_state", lambda: state)):
            run.side_effect = results
            return core.gh_api("/x"), run

    def test_retries_through_a_secondary_limit(self):
        out, run = self.call([self.result(1, SECONDARY_403), self.result(0, "")])
        self.assertEqual((out, run.call_count), ("ok", 2))

    def test_a_normal_failure_is_not_retried(self):
        with self.assertRaises(RuntimeError) as caught:
            self.call([self.result(1, NOT_FOUND_404)])
        self.assertNotIsInstance(caught.exception, core.RateLimited)

    def test_waits_at_least_a_minute_before_retrying(self):
        # GitHub asks for 60s minimum on a secondary limit; a faster schedule can
        # prolong the block.
        waits = []
        self.call([self.result(1, SECONDARY_403), self.result(1, ABUSE_403),
                   self.result(0, "")], waits=waits)
        self.assertEqual(waits, [core.SECONDARY_BACKOFF_SECONDS,
                                 core.SECONDARY_BACKOFF_SECONDS * 2])

    def test_an_exhausted_quota_fails_fast_rather_than_sleeping_it_out(self):
        # The hourly quota clears only at its reset, which no workflow step can
        # wait for.
        waits = []
        with self.assertRaises(core.RateLimited) as caught:
            self.call([self.result(1, PRIMARY_403)], quota=1800, waits=waits)
        self.assertEqual(waits, [])
        self.assertIn("1800s", str(caught.exception))

    def test_a_bare_429_with_no_message_is_still_a_rate_limit(self):
        # `gh` renders a response with no JSON message as "gh: HTTP 429".
        self.assertTrue(core._rate_limited("gh: HTTP 429"))

    def test_a_failed_quota_probe_is_not_read_as_room_to_spare(self):
        # /rate_limit does not cost primary quota but can cost secondary, so the
        # probe can itself be refused; reading that as "budget is fine" would keep
        # us issuing requests while limited.
        waits = []
        self.call([self.result(1, SECONDARY_403), self.result(0, "")],
                  quota=core.QUOTA_UNKNOWN, waits=waits)
        self.assertEqual(waits, [core.SECONDARY_BACKOFF_SECONDS])

    def test_the_breaker_holds_for_the_next_interval_not_the_first(self):
        # Releasing after 60s would let a looping caller restart the whole
        # schedule, which is what the breaker exists to prevent.
        before = core.time.time()
        with self.assertRaises(core.RateLimited):
            self.call([self.result(1, SECONDARY_403)] * core.RATE_LIMIT_ATTEMPTS)
        held = core._BLOCKED_UNTIL - before
        self.assertGreaterEqual(
            held, core.SECONDARY_BACKOFF_SECONDS * 2 ** (core.RATE_LIMIT_ATTEMPTS - 1))

    def test_a_short_block_never_shortens_a_long_one(self):
        core._BLOCKED_UNTIL = core.time.time() + 3600
        core._block_for(1)
        self.assertGreater(core._BLOCKED_UNTIL - core.time.time(), 3000)

    def test_a_quota_resetting_soon_is_waited_for(self):
        waits = []
        out, _ = self.call([self.result(1, PRIMARY_403), self.result(0, "")],
                           quota=20, waits=waits)
        self.assertEqual((out, waits), ("ok", [20]))

    def test_exhausting_the_attempts_raises_rate_limited(self):
        with self.assertRaises(core.RateLimited):
            self.call([self.result(1, SECONDARY_403)] * core.RATE_LIMIT_ATTEMPTS)

    def test_a_later_read_fails_fast_instead_of_waiting_again(self):
        # stuck_alerts runs ten detectors catching failures individually; without
        # this each would start the whole wait over and blow the job timeout.
        with self.assertRaises(core.RateLimited):
            self.call([self.result(1, SECONDARY_403)] * core.RATE_LIMIT_ATTEMPTS)
        with mock.patch.object(core.subprocess, "run") as run:
            with self.assertRaises(core.RateLimited):
                core.gh_api("/y")
            run.assert_not_called()


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
    @staticmethod
    def board(n, updated, association):
        return {
            "body": f'<!--tauceti-scoreboard--><!--tauceti-meta:v1 {{"n":{n}}}-->',
            "updated": updated,
            "author_association": association,
        }

    def test_parses_meta_with_nested_states(self):
        # Regression: a lazy `\{.*?\}` truncated at the first inner `}` and dropped the whole meta.
        body = ('<!--tauceti-scoreboard-->\n'
                '<!--tauceti-meta:v1 {"head_sha":"H","states":{"correctness":"blocking_block",'
                '"reuse":"green"},"full_rounds":2}--> trailing text')
        meta = core.scoreboard_meta_from([{"body": body, "updated": "2026-01-01"}])
        self.assertEqual(meta.get("states", {}).get("correctness"), "blocking_block")
        self.assertEqual(meta.get("full_rounds"), 2)

    def test_newest_supplied_comment_wins(self):
        old = {"body": '<!--tauceti-scoreboard--><!--tauceti-meta:v1 {"n":1}-->', "updated": "2026-01-01"}
        new = {"body": '<!--tauceti-scoreboard--><!--tauceti-meta:v1 {"n":2}-->', "updated": "2026-02-01"}
        self.assertEqual(core.scoreboard_meta_from([old, new]).get("n"), 2)

    def test_no_marker_is_empty(self):
        self.assertEqual(core.scoreboard_meta_from([{"body": "hi", "updated": "x"}]), {})

    def test_status_scoreboard_accepts_newer_contributor_review(self):
        comments = [
            self.board(1, "2026-01-01", "MEMBER"),
            self.board(2, "2026-02-01", "CONTRIBUTOR"),
        ]
        with mock.patch.object(core, "issue_comments", return_value=comments):
            self.assertEqual(core.scoreboard_meta("9").get("n"), 2)

    def test_destructive_selector_keeps_repo_associated_policy(self):
        comments = [
            self.board(1, "2026-01-01", "MEMBER"),
            self.board(2, "2026-02-01", "CONTRIBUTOR"),
        ]
        with mock.patch.object(core, "issue_comments", return_value=comments):
            self.assertEqual(core.repo_associated_scoreboard_meta("9").get("n"), 1)

    def test_issue_comment_fetch_has_no_author_filter(self):
        raw = json.dumps({
            "body": "external review",
            "updated": "2026-02-01",
            "author_association": "CONTRIBUTOR",
        })
        with mock.patch.object(core, "gh_api", return_value=raw) as gh:
            self.assertEqual(core.issue_comments("9")[0]["author_association"], "CONTRIBUTOR")
        self.assertNotIn("select(.author_association", gh.call_args.kwargs["jq"])


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

    def test_ci_failure_is_ci_failed(self):
        self.assertEqual(self.label(ci="failure"), "ci-failed")

    def test_green_changes_is_awaiting_author(self):
        self.assertEqual(self.label(ci="success", review="changes"), "awaiting-author")

    def test_a_red_build_outranks_the_review_verdict(self):
        # Both states want the author, but they are told apart on purpose: a red build is read in the
        # build log and a changes request in the review threads. A PR that is red AND has a changes
        # request shows ci-failed, because nothing about the review can be trusted until it builds.
        self.assertEqual(self.label(ci="failure", review="changes"), "ci-failed")
        self.assertEqual(self.label(ci="failure", review="approved"), "ci-failed")

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
        self.assertEqual(self.label(ci="failure", inprogress=True), "ci-failed")
        self.assertEqual(self.label(ci="success", review="changes", inprogress=True), "awaiting-author")
        self.assertEqual(self.label(ci="success", review="approved", inprogress=True), "ready-to-merge")


class Derive(unittest.TestCase):
    """core.derive glues pr_state/ci_status/issue_comments together; stub them."""

    def setUp(self):
        self._saved = (core.pr_state, core.ci_status, core.issue_comments)

    def tearDown(self):
        core.pr_state, core.ci_status, core.issue_comments = self._saved

    def stub(self, state="open", merged=False, ci="success", comments=None):
        core.pr_state = lambda pr: {"state": state, "merged": merged, "head": "H", "title": "T"}
        core.ci_status = lambda head: ci
        core.issue_comments = lambda pr: (comments or [])

    def test_contributor_scoreboard_drives_review_state(self):
        self.stub(comments=[{
            "body": ('<!--tauceti-scoreboard-->'
                     '<!--tauceti-meta:v1 {"head_sha":"H",'
                     '"states":{"correctness":"blocking_request"}}-->'),
            "updated": "2026-02-01",
            "author_association": "CONTRIBUTOR",
        }])
        self.assertEqual(core.derive("1")["review"], "changes")

    def test_contributor_inprogress_marker_drives_status(self):
        self.stub(ci="success",
                  comments=[{
                      "body": '<!--tauceti-review-in-progress {"head": "H", "expires_at": 9999999999}-->',
                      "author_association": "CONTRIBUTOR",
                  }])
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
        core.issue_comments = lambda pr: []
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


class EnsureLabel(unittest.TestCase):
    """A label is created once and then lives forever, so ensure_label has to keep an EXISTING
    label's colour and description in step with LABELS -- otherwise editing a description here
    would never reach GitHub and the live label would go on describing behaviour we changed."""

    def setUp(self):
        self._run = labels._run
        self.calls = []
        self.probe = None
        labels._run = self.fake_run

    def tearDown(self):
        labels._run = self._run

    def fake_run(self, args):
        self.calls.append(args)
        if args[0].startswith("/repos/") and len(args) == 1:      # the GET probe
            if self.probe is None:
                return SimpleNamespace(returncode=1, stdout="", stderr="gh: Not Found (HTTP 404)")
            return SimpleNamespace(returncode=0, stdout=json.dumps(self.probe), stderr="")
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    def methods(self):
        return [args[1] for args in self.calls if args[0] == "--method"]

    def test_absent_label_is_created(self):
        labels.ensure_label("ci-failed")
        self.assertEqual(self.methods(), ["POST"])

    def test_matching_label_is_left_alone(self):
        color, description = labels.LABELS["ci-failed"]
        self.probe = {"color": color, "description": description}
        labels.ensure_label("ci-failed")
        self.assertEqual(self.methods(), [])

    def test_drifted_description_is_patched(self):
        color, _ = labels.LABELS["awaiting-author"]
        self.probe = {"color": color, "description": "The build failed or a review requested changes"}
        labels.ensure_label("awaiting-author")
        self.assertEqual(self.methods(), ["PATCH"])

    def test_an_unreadable_probe_body_never_breaks_the_add(self):
        labels._run = lambda args: (
            self.calls.append(args)
            or SimpleNamespace(returncode=0, stdout="not json", stderr="")
        )
        labels.ensure_label("ci-failed")   # must not raise; presentation is cosmetic


if __name__ == "__main__":
    unittest.main()
