#!/usr/bin/env python3
"""Hermetic tests for scripts/pipeline_health.py."""

from __future__ import annotations

import unittest
from datetime import datetime, timedelta, timezone

import pipeline_health as health

UTC = timezone.utc
NOW = datetime(2026, 8, 25, 12, 0, tzinfo=UTC)


def iso(when: datetime) -> str:
    return when.strftime("%Y-%m-%dT%H:%M:%SZ")


def pr(number, events, *, state="OPEN", created=None, merged=None):
    """A PR with a lifecycle label timeline, as fetch_prs would return it."""
    return {
        "number": number,
        "created_at": iso(created or NOW - timedelta(days=1)),
        "merged_at": iso(merged) if merged else None,
        "closed_at": iso(merged) if merged else None,
        "state": state,
        "is_draft": False,
        "author": "someone",
        "labels": [events[-1][1]] if events and state == "OPEN" else [],
        "labeled_events": [
            {"created_at": iso(at), "label": label} for at, label in events
        ],
    }


def snapshot(prs):
    return {"schema_version": 1, "repo": "TauCetiProject/TauCeti",
            "fetched_at": iso(NOW), "prs": prs, "scoreboards": {}}


class IntervalTests(unittest.TestCase):
    def test_consecutive_labels_bound_each_spell(self):
        item = pr(1, [
            (NOW - timedelta(hours=10), "awaiting-CI"),
            (NOW - timedelta(hours=8), "awaiting-review"),
        ])
        spells = list(health.lifecycle_intervals(item, NOW))
        self.assertEqual([s[0] for s in spells], ["awaiting-CI", "awaiting-review"])
        self.assertEqual((spells[0][2] - spells[0][1]), timedelta(hours=2))

    def test_an_open_pr_s_last_spell_is_still_running(self):
        item = pr(1, [(NOW - timedelta(hours=3), "awaiting-review")])
        self.assertIsNone(list(health.lifecycle_intervals(item, NOW))[-1][2])

    def test_a_merged_pr_s_last_spell_ends_at_the_merge(self):
        merged = NOW - timedelta(hours=1)
        item = pr(2, [(NOW - timedelta(hours=5), "ready-to-merge")],
                  state="MERGED", merged=merged)
        _, start, end = list(health.lifecycle_intervals(item, NOW))[-1]
        self.assertEqual(end, merged)

    def test_non_lifecycle_labels_are_ignored(self):
        item = pr(3, [(NOW - timedelta(hours=4), "roadmap:algebra"),
                      (NOW - timedelta(hours=2), "awaiting-review")])
        self.assertEqual([s[0] for s in health.lifecycle_intervals(item, NOW)],
                         ["awaiting-review"])


class AnalysisTests(unittest.TestCase):
    def test_depth_counts_only_prs_still_in_the_stage(self):
        data = snapshot([
            pr(1, [(NOW - timedelta(hours=2), "awaiting-review")]),
            pr(2, [(NOW - timedelta(hours=3), "awaiting-review")]),
            pr(3, [(NOW - timedelta(hours=9), "awaiting-review"),
                   (NOW - timedelta(hours=1), "ready-to-merge")]),
        ])
        result = health.analyse(data, 24, 24 * 14, NOW)
        by_stage = {s["stage"]: s for s in result["stages"]}
        self.assertEqual(by_stage["awaiting-review"]["depth"], 2)
        self.assertEqual(by_stage["ready-to-merge"]["depth"], 1)

    def test_an_unfinished_spell_does_not_bias_dwell_times_downwards(self):
        """A PR still sitting in a stage has not finished waiting, so counting
        its time so far as a completed dwell would make a stuck stage look fast."""
        data = snapshot([
            pr(1, [(NOW - timedelta(hours=100), "awaiting-review")]),          # stuck
            pr(2, [(NOW - timedelta(hours=4), "awaiting-review"),
                   (NOW - timedelta(hours=3), "ready-to-merge")]),             # 1h, done
        ])
        stage = next(s for s in health.analyse(data, 24, 24 * 14, NOW)["stages"]
                     if s["stage"] == "awaiting-review")
        self.assertEqual(stage["median_dwell_hours"], 1.0)
        self.assertEqual(stage["oldest_waiting_hours"], 100.0)

    def test_author_owned_stages_are_marked_as_such(self):
        result = health.analyse(snapshot([]), 24, 24 * 14, NOW)
        owned = {s["stage"]: s["owned_by_project"] for s in result["stages"]}
        self.assertFalse(owned["ci-failed"])
        self.assertFalse(owned["awaiting-author"])
        self.assertTrue(owned["awaiting-review"])


class BottleneckTests(unittest.TestCase):
    def base(self, **overrides):
        result = {"merged_per_hour": 1.0, "baseline_merged_per_hour": 5.0, "stages": []}
        result.update(overrides)
        return result

    def stage(self, name, **kw):
        item = {"stage": name, "owned_by_project": name not in health.STATE_AUTHOR_ACTION,
                "depth": 0, "oldest_waiting_hours": 0.0, "entered_per_hour": 0.0,
                "left_per_hour": 0.0, "baseline_median_dwell_hours": None}
        item.update(kw)
        return item

    def test_healthy_throughput_names_no_bottleneck(self):
        self.assertIsNone(health.find_bottleneck(
            self.base(merged_per_hour=5.0, baseline_merged_per_hour=5.0)))

    def test_a_stage_filling_faster_than_it_drains_wins(self):
        result = self.base(stages=[
            self.stage("awaiting-CI", depth=50, entered_per_hour=1.0, left_per_hour=1.0),
            self.stage("awaiting-review", depth=10, entered_per_hour=3.0, left_per_hour=0.5),
        ])
        self.assertEqual(health.find_bottleneck(result)["stage"], "awaiting-review")

    def test_a_deep_but_draining_stage_is_not_the_bottleneck(self):
        """Depth alone means nothing: a queue can be long and perfectly healthy."""
        result = self.base(stages=[
            self.stage("awaiting-CI", depth=200, entered_per_hour=2.0, left_per_hour=2.5),
            self.stage("ready-to-merge", depth=3, entered_per_hour=1.0, left_per_hour=0.2),
        ])
        self.assertEqual(health.find_bottleneck(result)["stage"], "ready-to-merge")

    def test_stages_waiting_on_the_author_are_never_blamed(self):
        """The project cannot fix these, so naming one would point effort at
        exactly the wrong place."""
        result = self.base(stages=[
            self.stage("ci-failed", depth=99, entered_per_hour=9.0, left_per_hour=0.1),
            self.stage("awaiting-author", depth=99, entered_per_hour=9.0, left_per_hour=0.1),
        ])
        self.assertIsNone(health.find_bottleneck(result))

    def test_an_empty_stage_is_not_a_bottleneck(self):
        result = self.base(stages=[self.stage("awaiting-review", depth=0,
                                              entered_per_hour=0.0, left_per_hour=0.0)])
        self.assertIsNone(health.find_bottleneck(result))


class ReportTests(unittest.TestCase):
    def test_report_renders_and_names_the_author_owned_marker(self):
        result = health.analyse(snapshot([
            pr(1, [(NOW - timedelta(hours=2), "awaiting-review")]),
        ]), 24, 24 * 14, NOW)
        text = health.report(result)
        self.assertIn("awaiting-review", text)
        self.assertIn("waiting on the contributor", text)


if __name__ == "__main__":
    unittest.main()
