#!/usr/bin/env python3
"""Hermetic tests for scripts/pr_stats_graphs.py."""

from __future__ import annotations

import json
import shutil
import subprocess
import tempfile
import unittest
import xml.etree.ElementTree as ET
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
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
                    "number": 42, "createdAt": timestamp(1), "mergedAt": None,
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
            stats, "graphql", side_effect=[first_page, timeline_page, timeline_extra],
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
                    "number": 42, "createdAt": timestamp(1), "mergedAt": None,
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
                    "number": 42, "createdAt": timestamp(1), "mergedAt": timestamp(2),
                    "closedAt": timestamp(2), "state": "MERGED", "isDraft": False,
                    "author": {"login": "alice"}, "labels": {"nodes": []},
                }],
            }},
        }
        with patch.object(stats, "graphql", return_value=first_page) as graphql:
            prs = stats.fetch_prs("example/project")
        self.assertEqual(prs[0]["labeled_events"], [])
        self.assertEqual(graphql.call_count, 1)

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
        def comment(number, user, canonical=True, association="MEMBER"):
            return json.dumps({
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
            scoreboards, rejected = stats.fetch_scoreboards(
                "example/project", {7, 9},
                {"reviewer-a", "reviewer-b", "marker-quoter"},
            )
        self.assertEqual(
            [(item["pr"], item["user"]) for item in scoreboards],
            [(7, "reviewer-a"), (7, "reviewer-b")],
        )
        self.assertEqual(
            dict(rejected),
            {"not_a_pull_request": 1, "no_canonical_scoreboard_meta": 1,
             "untrusted_author": 1},
        )

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
            patch.object(stats, "fetch_scoreboards", return_value=([], {})) as fetch,
        ):
            stats.fetch_snapshot("example/project")
        fetch.assert_called_once_with(
            "example/project", {1, 2, 3}, {"merged-author"},
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
