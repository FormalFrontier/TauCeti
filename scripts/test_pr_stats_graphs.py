#!/usr/bin/env python3
"""Hermetic tests for scripts/pr_stats_graphs.py."""

from __future__ import annotations

import json
from collections import Counter
import shutil
import subprocess
import tempfile
import unittest
import xml.etree.ElementTree as ET
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import chart_style
import pr_stats_graphs as stats


UTC = timezone.utc


def timestamp(day: int, hour: int = 0) -> str:
    return datetime(2026, 1, day, hour, tzinfo=UTC).isoformat().replace("+00:00", "Z")


def pr(number, created_day, *, state="CLOSED", merged_day=None, author="alice",
       labels=(), cycles=0, is_draft=False):
    events = []
    for index in range(cycles):
        day = created_day + index
        if index:
            # The author's turn between rounds; without it the next label continues one cycle.
            events.append({"created_at": timestamp(day, 6), "label": "awaiting-author"})
        events.append({"created_at": timestamp(day, 8), "label": "awaiting-review"})
        # Claiming the round and having the label restored is churn inside the same cycle.
        events.append({"created_at": timestamp(day, 9), "label": "review-in-progress"})
        events.append({"created_at": timestamp(day, 10), "label": "awaiting-review"})
    if "awaiting-author" in labels:
        events.append({"created_at": timestamp(13, 12), "label": "awaiting-author"})
    if "review-in-progress" in labels and not cycles:
        events.append({"created_at": timestamp(13, 10), "label": "review-in-progress"})
    return {
        "number": number,
        "created_at": timestamp(created_day),
        "updated_at": timestamp(merged_day or 14, 12),
        "merged_at": timestamp(merged_day, 12) if merged_day else None,
        "closed_at": timestamp(merged_day, 12) if merged_day else None,
        "state": state,
        "is_draft": is_draft,
        "author": author,
        "labels": list(labels),
        "labeled_events": events,
    }


class MetricsTest(unittest.TestCase):
    def test_outer_pr_page_contains_no_nested_timeline(self):
        self.assertIn("pullRequests(first:100", stats.PR_PAGE_QUERY)
        self.assertNotIn("timelineItems", stats.PR_PAGE_QUERY)

    def test_direct_label_timeline_pagination_is_not_truncated(self):
        first_page = {
            "repository": {"pullRequests": {
                "pageInfo": {"hasNextPage": False, "endCursor": None},
                "nodes": [{
                    "number": 42, "createdAt": timestamp(1), "updatedAt": timestamp(3),
                    "mergedAt": None,
                    "closedAt": None, "state": "OPEN", "isDraft": False,
                    "author": {"login": "alice"}, "labels": {"nodes": []},
                }],
            }},
        }
        timeline_page = {
            "repository": {"pullRequest": {"timelineItems": {
                "pageInfo": {"hasNextPage": True, "endCursor": "events-100"},
                "nodes": [{"createdAt": timestamp(2),
                           "label": {"name": "awaiting-review"}}],
            }, "mergedAt": None, "closedAt": None, "state": "OPEN",
                "isDraft": False, "labels": {"nodes": []}}},
        }
        timeline_extra = {
            "repository": {"pullRequest": {"timelineItems": {
                "pageInfo": {"hasNextPage": False, "endCursor": None},
                "nodes": [{"createdAt": timestamp(3),
                           "label": {"name": "awaiting-review"}}],
            }, "mergedAt": None, "closedAt": None, "state": "OPEN",
                "isDraft": False,
                "labels": {"nodes": [{"name": "awaiting-review"}]}}},
        }
        with patch.object(
            stats, "graphql",
            side_effect=[first_page, timeline_page, timeline_extra],
        ):
            prs = stats.fetch_prs("example/project")
        self.assertEqual(
            [event["label"] for event in prs[0]["labeled_events"]],
            ["awaiting-review", "awaiting-review"],
        )
        self.assertEqual(prs[0]["labels"], ["awaiting-review"])

    def test_closed_pr_uses_complete_direct_timeline(self):
        first_page = {
            "repository": {"pullRequests": {
                "pageInfo": {"hasNextPage": False, "endCursor": None},
                "nodes": [{
                    "number": 42, "createdAt": timestamp(1), "updatedAt": timestamp(3),
                    "mergedAt": None,
                    "closedAt": timestamp(14), "state": "CLOSED", "isDraft": False,
                    "author": {"login": "alice"},
                    "labels": {"nodes": [{"name": "roadmap/PDE"}]},
                }],
            }},
        }
        direct = {
            "repository": {"pullRequest": {"timelineItems": {
                "pageInfo": {"hasNextPage": False, "endCursor": None},
                "nodes": [
                    {"createdAt": timestamp(min(index + 1, 14)),
                     "label": {"name": "awaiting-review"}}
                    for index in range(9)
                ],
            }, "mergedAt": None, "closedAt": timestamp(14), "state": "CLOSED",
                "isDraft": False,
                "labels": {"nodes": [{"name": "roadmap/PDE"}]}}},
        }
        with patch.object(stats, "LIFECYCLE_EPOCH", datetime(2026, 1, 1, tzinfo=UTC)):
            with patch.object(stats, "graphql", side_effect=[first_page, direct]):
                prs = stats.fetch_prs("example/project")
        self.assertEqual(len(prs[0]["labeled_events"]), 9)

    def test_pr_closed_before_lifecycle_epoch_skips_timeline(self):
        first_page = {
            "repository": {"pullRequests": {
                "pageInfo": {"hasNextPage": False, "endCursor": None},
                "nodes": [{
                    "number": 42, "createdAt": timestamp(1), "updatedAt": timestamp(2),
                    "mergedAt": timestamp(2),
                    "closedAt": timestamp(2), "state": "MERGED", "isDraft": False,
                    "author": {"login": "alice"}, "labels": {"nodes": []},
                }],
            }},
        }
        with patch.object(stats, "graphql", return_value=first_page) as graphql:
            prs = stats.fetch_prs("example/project")
        self.assertEqual(prs[0]["labeled_events"], [])
        self.assertEqual(graphql.call_count, 1)

    # --- timelines are fetched one at a time, on purpose --------------------------------------
    #
    # Aliasing several pull requests into one GraphQL request is much cheaper and silently
    # returns incomplete timelines. Measured on 2026-09-06: in a 50-alias batch PR #1556 came
    # back with 2 label events and `hasNextPage: false` where the paginating query returns 4,
    # the missing one being its current `ci-failed`. Smaller batches were complete for that
    # sample, so the limit follows total requested nodes and cannot be pinned to a size, and
    # `hasNextPage` is computed against the truncated slice so nothing in the response reveals
    # the loss. This test exists so the optimisation cannot be reintroduced without meeting it.

    def test_each_pull_request_gets_its_own_query(self):
        numbers = [1, 2, 3]
        reply = {"repository": {"pullRequest": {
            "timelineItems": {"pageInfo": {"hasNextPage": False, "endCursor": None},
                              "nodes": [{"createdAt": timestamp(2),
                                         "label": {"name": "awaiting-review"}}]},
            "mergedAt": None, "closedAt": None, "state": "OPEN", "isDraft": False,
            "labels": {"nodes": [{"name": "awaiting-review"}]}}}}
        with patch.object(stats, "graphql", return_value=reply) as graphql:
            result, fetched = stats.fetch_timelines("o", "n", numbers)
        self.assertEqual(graphql.call_count, 3)
        self.assertEqual(fetched, 3)
        self.assertEqual(len(result), 3)
        # Each call names exactly one pull request.
        for call in graphql.call_args_list:
            self.assertIn("number", call.kwargs)

    def test_the_module_defines_no_alias_batching_helper(self):
        for name in ("timeline_batch_query", "TIMELINE_BATCH"):
            self.assertFalse(
                hasattr(stats, name),
                f"{name} is back. Aliased batching returns silently truncated timelines with "
                "hasNextPage false; read the note above fetch_timeline before reinstating it.")

    def test_reused_pull_requests_are_not_fetched(self):
        numbers = [1, 2, 3]
        reusable = {1: {"merged_at": None, "closed_at": None, "state": "OPEN",
                        "is_draft": False, "labels": [], "labeled_events": []}}
        reply = {"repository": {"pullRequest": {
            "timelineItems": {"pageInfo": {"hasNextPage": False, "endCursor": None}, "nodes": []},
            "mergedAt": None, "closedAt": None, "state": "OPEN", "isDraft": False,
            "labels": {"nodes": []}}}}
        with patch.object(stats, "graphql", return_value=reply) as graphql:
            result, fetched = stats.fetch_timelines("o", "n", numbers, reusable)
        self.assertEqual(graphql.call_count, 2)
        self.assertEqual(fetched, 2)
        self.assertEqual(len(result), 3)

    # --- incremental snapshots -------------------------------------------------------------
    #
    # One GraphQL request per pull request, against an hourly budget of 5000 points, is a wall
    # this repository walked into: by September 2026 a full pass needed about 4600 requests and
    # the charts ahead of it in the Pages job spent the rest, so the snapshot stopped being
    # written at all and the published pipeline-health.json simply never appeared. Reuse is what
    # keeps a run proportional to what changed rather than to how big the project has become, so
    # these tests pin down both that it happens and that it cannot serve stale events.

    OPEN_PAGE = {
        "repository": {"pullRequests": {
            "pageInfo": {"hasNextPage": False, "endCursor": None},
            "nodes": [{
                "number": 42, "createdAt": timestamp(1), "updatedAt": timestamp(3),
                "mergedAt": None, "closedAt": None, "state": "OPEN", "isDraft": False,
                "author": {"login": "alice"},
                "labels": {"nodes": [{"name": "awaiting-review"}]},
            }],
        }},
    }

    def snapshot_with(self, updated_at, events):
        return {"repo": "example/project", "fetched_at": timestamp(3), "prs": [{
            "number": 42, "updated_at": updated_at, "merged_at": None, "closed_at": None,
            "state": "OPEN", "is_draft": False, "labels": ["awaiting-review"],
            "labeled_events": events,
        }]}

    def test_unchanged_pr_reuses_its_recorded_timeline(self):
        events = [{"created_at": timestamp(2), "label": "awaiting-review"}]
        previous = self.snapshot_with(timestamp(3), events)
        with patch.object(stats, "graphql", side_effect=[self.OPEN_PAGE]) as graphql:
            prs = stats.fetch_prs("example/project", previous)
        # One call: the page query. The timeline query never ran.
        self.assertEqual(graphql.call_count, 1)
        self.assertEqual(prs[0]["labeled_events"], events)

    def test_touched_pr_is_refetched(self):
        # The snapshot was taken when the PR last changed on day 2; it has changed since.
        previous = self.snapshot_with(
            timestamp(2), [{"created_at": timestamp(2), "label": "awaiting-review"}])
        direct = {"repository": {"pullRequest": {
            "timelineItems": {"pageInfo": {"hasNextPage": False, "endCursor": None},
                              "nodes": [{"createdAt": timestamp(3),
                                         "label": {"name": "awaiting-review"}}]},
            "mergedAt": None, "closedAt": None, "state": "OPEN", "isDraft": False,
            "labels": {"nodes": [{"name": "awaiting-review"}]}}}}
        with patch.object(stats, "graphql", side_effect=[self.OPEN_PAGE, direct]) as graphql:
            prs = stats.fetch_prs("example/project", previous)
        self.assertEqual(graphql.call_count, 2)
        self.assertEqual(prs[0]["labeled_events"],
                         [{"created_at": timestamp(3), "label": "awaiting-review"}])

    def test_reuse_keeps_the_current_labels_not_the_recorded_ones(self):
        # A reused entry supplies only the event list. Its state fields come from this run's
        # page query, which was read later. Here the recorded copy disagrees, and must lose.
        previous = self.snapshot_with(
            timestamp(3), [{"created_at": timestamp(2), "label": "awaiting-review"}])
        previous["prs"][0]["labels"] = ["ready-to-merge"]
        previous["prs"][0]["state"] = "MERGED"
        with patch.object(stats, "graphql", side_effect=[self.OPEN_PAGE]):
            prs = stats.fetch_prs("example/project", previous)
        self.assertEqual(prs[0]["labels"], ["awaiting-review"])
        self.assertEqual(prs[0]["state"], "OPEN")

    def test_snapshot_without_update_times_is_not_reused(self):
        # A snapshot written before updated_at was recorded carries no certificate that its
        # events are current, so it must fall back to a full walk rather than be trusted.
        previous = self.snapshot_with(timestamp(3), [])
        del previous["prs"][0]["updated_at"]
        self.assertEqual(stats.reusable_timelines(previous, [
            {"number": 42, "updated_at": timestamp(3), "merged_at": None, "closed_at": None,
             "state": "OPEN", "is_draft": False, "labels": []}]), {})

    def test_snapshot_from_another_repository_is_ignored(self):
        previous = self.snapshot_with(timestamp(3), [])
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "snapshot.json"
            path.write_text(json.dumps(previous))
            self.assertIsNone(stats.load_previous(path, "someone/else"))
            self.assertIsNotNone(stats.load_previous(path, "example/project"))

    def test_a_missing_or_corrupt_snapshot_is_not_fatal(self):
        with tempfile.TemporaryDirectory() as directory:
            missing = Path(directory) / "absent.json"
            self.assertIsNone(stats.load_previous(missing, "example/project"))
            corrupt = Path(directory) / "corrupt.json"
            corrupt.write_text("{not json")
            self.assertIsNone(stats.load_previous(corrupt, "example/project"))

    def test_run_gh_waits_for_the_budget_instead_of_failing(self):
        # Three retries one, two and four seconds apart cannot refill an hourly budget, so the
        # original behaviour turned "wait a while" into "this run produces nothing".
        results = [
            SimpleNamespace(returncode=1, stdout="",
                            stderr="gh: API rate limit already exceeded for site ID installation."),
            SimpleNamespace(returncode=0, stdout="done", stderr=""),
        ]
        with patch.object(stats.subprocess, "run", side_effect=results) as run:
            with patch.object(stats, "rate_limit_reset_wait", return_value=42.0):
                with patch.object(stats.time, "sleep") as sleep:
                    self.assertEqual(stats.run_gh(["api", "graphql"]), "done")
        self.assertEqual(run.call_count, 2)
        sleep.assert_called_once_with(42.0)

    def test_run_gh_gives_up_when_the_budget_will_not_refill(self):
        limited = SimpleNamespace(
            returncode=1, stdout="", stderr="gh: API rate limit already exceeded")
        with patch.object(stats.subprocess, "run", return_value=limited):
            with patch.object(stats, "rate_limit_reset_wait", return_value=None):
                with self.assertRaises(RuntimeError) as caught:
                    stats.run_gh(["api", "graphql"])
        self.assertIn("--since-data", str(caught.exception))

    def test_review_cycles_use_label_transitions_and_reach_seven(self):
        prs = [
            pr(1, 1, cycles=0),
            pr(2, 2, cycles=1),
            pr(3, 3, cycles=2),
            pr(4, 4, cycles=7),
        ]
        result = stats.review_cycle_metrics(prs)
        self.assertEqual(result["total_cycles"], 10)
        self.assertEqual(result["reviewed_prs"], 3)
        self.assertEqual(
            [item["prs"] for item in result["reach"]],
            [3, 2, 1, 1, 1, 1, 1],
        )

    def test_restored_awaiting_review_label_stays_in_the_same_cycle(self):
        item = pr(1, 1)
        item["labeled_events"] = [
            {"created_at": timestamp(2, 1), "label": "awaiting-review"},
            {"created_at": timestamp(2, 2), "label": "review-in-progress"},
            # Reconciliation restores the label without the author having acted.
            {"created_at": timestamp(2, 3), "label": "awaiting-review"},
            {"created_at": timestamp(2, 4), "label": "awaiting-author"},
            {"created_at": timestamp(3, 1), "label": "awaiting-CI"},
            {"created_at": timestamp(3, 2), "label": "awaiting-review"},
        ]
        result = stats.review_cycle_metrics([item])
        self.assertEqual(result["total_cycles"], 2)
        self.assertEqual(result["cycles_by_pr"], {"1": 2})
        self.assertEqual(result["label_epoch"], "2026-01-02")

    def test_in_review_clock_survives_the_review_label_swap(self):
        item = pr(1, 1, state="OPEN", labels=("awaiting-review",))
        item["labeled_events"] = [
            {"created_at": timestamp(10, 0), "label": "awaiting-review"},
            {"created_at": timestamp(12, 0), "label": "review-in-progress"},
            {"created_at": timestamp(14, 0), "label": "awaiting-review"},
        ]
        metrics = stats.queue_age_metrics([item], datetime(2026, 1, 15, tzinfo=UTC))
        self.assertEqual(metrics["in_review_hours"], [120.0])
        self.assertEqual(metrics["missing_transition_fallbacks"], 0)

    def test_queue_age_order_and_state_clocks(self):
        snapshot = datetime(2026, 1, 15, tzinfo=UTC)
        prs = [
            pr(1, 10, state="OPEN", labels=("awaiting-author",)),
            pr(2, 11, state="OPEN", labels=("review-in-progress",), cycles=2),
            pr(3, 12, state="OPEN", labels=("awaiting-CI",)),
            pr(4, 12, state="OPEN", labels=("awaiting-author",), is_draft=True),
        ]
        metrics = stats.queue_age_metrics(prs, snapshot)
        self.assertEqual(len(metrics["total_open_hours"]), 4)
        self.assertEqual(len(metrics["awaiting_author_hours"]), 1)
        self.assertEqual(len(metrics["in_review_hours"]), 1)
        self.assertEqual(metrics["other_open_prs"], 2)

    def test_author_clock_survives_the_awaiting_author_to_ci_failed_split(self):
        # The migration that introduced ci-failed relabels PRs that were already waiting on their
        # author. That is the same wait continuing, not a new one, so the clock must still run from
        # the original awaiting-author and not reset to the relabelling instant.
        item = pr(1, 1, state="OPEN", labels=("ci-failed",))
        item["labeled_events"] = [
            {"created_at": timestamp(1, 0), "label": "awaiting-author"},
            {"created_at": timestamp(4, 0), "label": "ci-failed"},
        ]
        metrics = stats.queue_age_metrics([item], datetime(2026, 1, 5, tzinfo=UTC))
        self.assertEqual(metrics["awaiting_author_hours"], [96.0])
        self.assertEqual(metrics["missing_transition_fallbacks"], 0)

    def test_author_clock_restarts_when_the_pr_goes_back_through_ci(self):
        # A push is a real fresh wait: the author acted, CI judged it, and it failed again.
        item = pr(1, 1, state="OPEN", labels=("ci-failed",))
        item["labeled_events"] = [
            {"created_at": timestamp(1, 0), "label": "awaiting-author"},
            {"created_at": timestamp(2, 0), "label": "awaiting-CI"},
            {"created_at": timestamp(4, 0), "label": "ci-failed"},
        ]
        metrics = stats.queue_age_metrics([item], datetime(2026, 1, 5, tzinfo=UTC))
        self.assertEqual(metrics["awaiting_author_hours"], [24.0])
        self.assertEqual(metrics["missing_transition_fallbacks"], 0)

    def test_current_state_clock_rejects_stale_historical_transition(self):
        item = pr(1, 1, state="OPEN", labels=("awaiting-review",), cycles=1)
        item["labeled_events"].append({
            "created_at": timestamp(3), "label": "ready-to-merge",
        })
        metrics = stats.queue_age_metrics(
            [item], datetime(2026, 1, 5, tzinfo=UTC),
        )
        self.assertEqual(metrics["missing_transition_fallbacks"], 1)
        self.assertEqual(metrics["in_review_hours"], [96.0])

    def test_generation_rejects_excessive_missing_state_transitions(self):
        prs = [
            pr(number, number, state="OPEN", labels=("awaiting-author",))
            for number in range(1, 4)
        ]
        for item in prs:
            item["labeled_events"] = []
        data = {
            "repo": "example/project", "fetched_at": timestamp(15),
            "prs": prs, "scoreboards": [],
        }
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaisesRegex(ValueError, "matching label transitions"):
                stats.generate(data, Path(temporary))

    def test_scoreboards_need_trust_pull_request_and_matching_meta(self):
        counter = iter(range(1000, 2000))

        def comment(number, user, canonical=True, association="MEMBER"):
            return json.dumps({
                "id": next(counter),
                "number": str(number), "created_at": timestamp(2),
                "updated_at": timestamp(2), "user": user, "canonical": canonical,
                "author_association": association,
            })

        raw = "\n".join([
            # GitHub Actions may project a real collaborator as CONTRIBUTOR here.
            comment(7, "reviewer-a", association="CONTRIBUTOR"),
            comment(8, "issue-commenter"),       # an ordinary issue, not a PR
            comment(9, "marker-quoter", False),  # the public marker without engine meta
            comment(7, "forger", association="NONE"),
            comment(7, "reviewer-b"),
        ])
        with patch.object(stats, "run_gh", return_value=raw):
            scoreboards, rejected, scanned_at = stats.fetch_scoreboards(
                "example/project", {7, 9},
                {"reviewer-a", "reviewer-b", "marker-quoter"},
            )
        self.assertTrue(scanned_at)
        self.assertEqual(
            [(item["pr"], item["user"]) for item in scoreboards],
            [(7, "reviewer-a"), (7, "reviewer-b")],
        )
        # Rejections are kept per comment id; the published counts are derived from them.
        self.assertEqual(
            dict(Counter(rejected.values())),
            {"not_a_pull_request": 1, "no_canonical_scoreboard_meta": 1,
             "untrusted_author": 1},
        )

    # --- incremental scoreboard scanning -----------------------------------------------------
    #
    # The comment scan reads the whole repository history: ~136 pages every three hours, and on
    # a course to break outright. GitHub caps this endpoint at 400 pages and the scan was
    # ASCENDING, so once the repository passes 40,000 comments the pages that stop arriving are
    # the newest -- the scoreboards that decide whether a pull request may merge. Descending plus
    # `since` fixes both the cost and the direction of that eventual loss.

    @staticmethod
    def scan(raw, previous=None, now=None):
        with patch.object(stats, "run_gh", return_value=raw) as run:
            result = stats.fetch_scoreboards(
                "example/project", {7}, {"trusted"}, previous,
                now or datetime(2026, 1, 10, tzinfo=UTC))
        return result, run.call_args.args[0][2]

    @staticmethod
    def row(identifier, number=7, user="trusted", canonical=True, day=2):
        return json.dumps({
            "id": identifier, "number": str(number), "created_at": timestamp(day),
            "updated_at": timestamp(day), "user": user, "canonical": canonical,
        })

    @staticmethod
    def snapshot(scanned_day=9, entries=(("1", 7, "trusted"),), rejected=None, ids=True):
        return {
            "scoreboards_scanned_at": timestamp(scanned_day),
            "scoreboards": [
                ({"id": i} if ids else {}) | {
                    "pr": pr_number, "created_at": timestamp(2),
                    "updated_at": timestamp(2), "user": user}
                for i, pr_number, user in entries],
            "rejected_scoreboard_comments_by_id": dict(rejected or {}),
        }

    def test_the_scan_is_descending_so_a_future_cap_loses_the_oldest(self):
        (_, _, _), path = self.scan("")
        self.assertIn("direction=desc", path)

    def test_no_previous_snapshot_scans_everything(self):
        (_, _, _), path = self.scan("")
        self.assertNotIn("since=", path)

    def test_a_recent_snapshot_scans_only_since_it(self):
        (boards, _, _), path = self.scan(self.row(2), previous=self.snapshot())
        self.assertIn("since=", path)
        # The carried-over entry survives alongside the newly seen one.
        self.assertEqual(sorted(item["id"] for item in boards), ["1", "2"])

    def test_the_since_is_pulled_back_before_the_last_scan(self):
        # A comment written while the previous scan was running must not fall in the gap.
        (_, _, _), path = self.scan("", previous=self.snapshot(scanned_day=9))
        self.assertIn("since=2026-01-08T23", path)

    def test_a_stale_snapshot_forces_a_full_rescan(self):
        # Deletions are invisible to an incremental scan, so one cannot be carried indefinitely.
        stale = self.snapshot(scanned_day=1)
        (boards, _, _), path = self.scan("", previous=stale)
        self.assertNotIn("since=", path)
        self.assertEqual(boards, [])

    def test_a_snapshot_without_comment_ids_forces_a_full_rescan(self):
        # Without ids there is no way to revise one comment's verdict, so nothing may be kept.
        (boards, _, _), path = self.scan("", previous=self.snapshot(ids=False))
        self.assertNotIn("since=", path)
        self.assertEqual(boards, [])

    def test_an_edited_comment_replaces_its_own_earlier_verdict(self):
        # Edited from a valid scoreboard into something untrusted: it must leave the kept set
        # and be counted once as rejected, not counted twice or left in both.
        previous = self.snapshot(entries=(("1", 7, "trusted"),))
        (boards, rejected, _), _ = self.scan(
            self.row("1", user="stranger"), previous=previous)
        self.assertEqual(boards, [])
        self.assertEqual(rejected, {"1": "untrusted_author"})

    def test_a_rejection_that_becomes_valid_stops_being_counted(self):
        previous = self.snapshot(entries=(), rejected={"1": "untrusted_author"})
        (boards, rejected, _), _ = self.scan(self.row("1"), previous=previous)
        self.assertEqual(rejected, {})
        self.assertEqual([item["id"] for item in boards], ["1"])

    def test_scoreboard_meta_pr_number_is_matched_exactly(self):
        # #185's scoreboard pasted onto #18 shares the prefix `"pr":18`, and a string "18"
        # is not the integer the engine writes; neither may be read as #18's own scoreboard.
        for meta in ({"kind": "scoreboard", "pr": 185}, {"kind": "scoreboard", "pr": "18"}):
            self.assertFalse(stats.names_scoreboard_for([json.dumps(meta)], 18), meta)
        self.assertTrue(
            stats.names_scoreboard_for(
                ["not json", json.dumps({"kind": "scoreboard", "pr": 18, "round": 2})], 18,
            )
        )

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_scoreboard_jq_program_executes_and_validates_metadata(self):
        def fixture(number, user, association, meta):
            body = f'<!--tauceti-scoreboard-->\n<!--tauceti-meta:v1 {json.dumps(meta)} -->'
            return {
                "id": 5000 + number,
                "issue_url": f"https://api.github.com/repos/example/project/issues/{number}",
                "created_at": timestamp(2), "updated_at": timestamp(3),
                "user": {"login": user}, "author_association": association,
                "body": body,
            }

        comments = [
            fixture(7, "trusted", "CONTRIBUTOR",
                    {"kind": "scoreboard", "pr": 7, "states": {"api": "green"}}),
            fixture(7, "wrong-pr", "MEMBER", {"kind": "scoreboard", "pr": 8}),
            fixture(7, "string-pr", "MEMBER", {"kind": "scoreboard", "pr": "7"}),
            fixture(7, "wrong-kind", "MEMBER", {"kind": "claim", "pr": 7}),
            {
                "id": 5099,
                "issue_url": "https://api.github.com/repos/example/project/issues/7",
                "created_at": timestamp(2), "updated_at": timestamp(3),
                "user": {"login": "missing-meta"}, "author_association": "MEMBER",
                "body": "<!--tauceti-scoreboard-->",
            },
        ]
        with patch.object(stats, "run_gh", return_value="") as run:
            stats.fetch_scoreboards("example/project", {7}, {"trusted"})
        query = run.call_args.args[0][-1]
        result = subprocess.run(
            ["jq", "-c", query], input=json.dumps(comments), text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
        )
        rows = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(
            [row["canonical"] for row in rows], [True, False, False, False, False],
        )
        self.assertEqual(rows[0]["user"], "trusted")

    def test_snapshot_trusts_only_merged_pr_authors(self):
        prs = [
            pr(1, 1, merged_day=2, author="merged-author"),
            pr(2, 2, state="OPEN", author="open-author"),
            pr(3, 3, merged_day=4, author="unknown"),
        ]
        with (
            patch.object(stats, "fetch_prs", return_value=prs),
            patch.object(stats, "fetch_scoreboards",
                         return_value=([], {}, timestamp(3))) as fetch,
        ):
            stats.fetch_snapshot("example/project")
        fetch.assert_called_once_with(
            "example/project", {1, 2, 3}, {"merged-author"}, None,
        )

    def test_thousands_of_contributors_are_bounded(self):
        start = datetime(2026, 1, 1, tzinfo=UTC)
        events = []
        for index in range(2_500):
            # Deterministic unequal totals make the selected top contributors stable.
            events.extend((start + timedelta(days=index % 7), f"user-{index:04d}")
                          for _ in range(1 + index % 3))
        dates, names, series, totals = stats.cumulative_chart_series(
            events, start.date(), date(2026, 1, 14), limit=12,
        )
        self.assertEqual(len(totals), 2_500)
        self.assertEqual(len(names), 13)  # top 12 + one bounded aggregate
        self.assertEqual(len(series), 13)
        self.assertTrue(names[-1].startswith("Other (2,488 contributors)"))
        self.assertTrue(all(len(values) == len(dates) for values in series.values()))


class RenderingTest(unittest.TestCase):
    def test_generate_writes_five_valid_svgs_with_requested_names(self):
        prs = [
            pr(1, 1, merged_day=2, author="alice", cycles=1),
            pr(2, 2, merged_day=5, author="bob", cycles=2),
            pr(3, 3, merged_day=9, author="alice", cycles=7),
            pr(4, 10, state="OPEN", labels=("awaiting-author",), author="carol"),
            pr(5, 11, state="OPEN", labels=("review-in-progress",), cycles=2,
               author="dave"),
            pr(6, 12, state="OPEN", labels=("awaiting-CI",), author="erin"),
            pr(7, 14, merged_day=15, author="frank", cycles=1),
        ]
        future_merge = pr(8, 14, author="future-author", cycles=1)
        future_merge.update({
            "merged_at": timestamp(15, 21), "closed_at": timestamp(15, 21),
            "state": "MERGED",
        })
        prs.append(future_merge)
        data = {
            "schema_version": 1,
            "repo": "example/project",
            "fetched_at": timestamp(15, 20),
            "prs": prs,
            "scoreboards": [
                {"pr": 1, "created_at": timestamp(2), "updated_at": timestamp(2),
                 "user": "reviewer-a"},
                {"pr": 2, "created_at": timestamp(5), "updated_at": timestamp(5),
                 "user": "reviewer-b"},
                {"pr": 7, "created_at": timestamp(15, 12),
                 "updated_at": timestamp(15, 12), "user": "reviewer-c"},
                {"pr": 8, "created_at": timestamp(15, 21),
                 "updated_at": timestamp(15, 21), "user": "future-reviewer"},
            ],
        }
        expected = [
            "pr-queue-age.svg",
            "review-cycles-reached.svg",
            "rolling-seven-day-history.svg",
            "cumulative-merges-by-contributor.svg",
            "cumulative-reviews-by-contributor.svg",
        ]
        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary)
            metrics = stats.generate(data, out, contributor_limit=2, history_days=30)
            for name in expected:
                root = ET.parse(out / name).getroot()
                svg = (out / name).read_text(encoding="utf-8")
                card = root.find("{http://www.w3.org/2000/svg}rect")
                self.assertIsNotNone(card)
                self.assertEqual(card.attrib["fill"], chart_style.BG)
                self.assertEqual(card.attrib["stroke"], chart_style.PANEL)
                self.assertGreater(float(card.attrib["rx"]), 0)
                width = int(root.attrib["viewBox"].split()[2])
                self.assertIn(chart_style.base_css(width), svg)
            self.assertTrue((out / "pr-stats.json").is_file())
            queue_svg = (out / "pr-queue-age.svg").read_text(encoding="utf-8")
            self.assertLess(queue_svg.index("Total time open"),
                            queue_svg.index("Awaiting author"))
            self.assertLess(queue_svg.index("Awaiting author"),
                            queue_svg.index("In review"))
            cycle_svg = (out / "review-cycles-reached.svg").read_text(encoding="utf-8")
            self.assertIn("Review cycle 7", cycle_svg)
            review_svg = (
                out / "cumulative-reviews-by-contributor.svg"
            ).read_text(encoding="utf-8")
            self.assertIn("Reviews by contributor", review_svg)
            self.assertNotIn("Trusted v1 review scoreboards", review_svg)
            self.assertEqual(metrics["review_cycles"]["max_cycle"], 7)
            self.assertEqual(metrics["merge_totals_by_contributor"]["frank"], 1)
            self.assertEqual(metrics["review_totals_by_contributor"]["reviewer-c"], 1)
            self.assertNotIn("future-author", metrics["merge_totals_by_contributor"])
            self.assertNotIn("future-reviewer", metrics["review_totals_by_contributor"])

    def test_render_failure_keeps_previous_asset_set(self):
        data = {
            "repo": "example/project", "fetched_at": timestamp(15),
            "prs": [pr(1, 1, merged_day=2, cycles=1)], "scoreboards": [],
        }
        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary) / "assets"
            out.mkdir()
            existing = out / "pr-queue-age.svg"
            existing.write_text("previous", encoding="utf-8")
            with patch.object(
                stats, "render_review_cycles", side_effect=RuntimeError("boom"),
            ):
                with self.assertRaisesRegex(RuntimeError, "boom"):
                    stats.generate(data, out)
            self.assertEqual(existing.read_text(encoding="utf-8"), "previous")
            self.assertFalse((out / "review-cycles-reached.svg").exists())


class SiteStatsPageTest(unittest.TestCase):
    """The page keeps the user-requested narrative and chart order."""

    def test_participation_precedes_contributor_histories(self):
        source = (
            Path(__file__).parents[1] / "web" / "Site" / "Stats.lean"
        ).read_text(encoding="utf-8")
        self.assertLess(
            source.index('src="static/rolling-seven-day-history.svg"'),
            source.index('src="static/review-cycles-reached.svg"'),
        )
        self.assertLess(
            source.rindex(":::blob participationGraph"),
            source.rindex(":::blob contributorGraphs"),
        )


if __name__ == "__main__":
    unittest.main()
