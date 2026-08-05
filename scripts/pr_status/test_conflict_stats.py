#!/usr/bin/env python3
"""Unit tests for the git replay that reconstructs historical merge conflicts.

Pure logic only: the git mirror is a fake, so these run with no network, no
`git`, and no repository. Run with:  python3 test_conflict_stats.py
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import conflict_stats  # noqa: E402


class Replay(unittest.TestCase):
    """conflict_stats replays merges against a fake `main` history."""

    class FakeMirror:
        """`conflicting_from` is the index in `history` from which `head` breaks."""

        def __init__(self, heads, breaks_at):
            self.heads = heads
            self.breaks_at = breaks_at
            self.merges = 0

        def pr_heads(self, number):
            return self.heads

        def conflicts(self, base_sha, head_sha):
            self.merges += 1
            at = self.breaks_at.get(head_sha)
            return at is not None and int(base_sha) >= at

    HISTORY = [(str(i), 1000 + 100 * i) for i in range(20)]
    TIMES = [when for _, when in HISTORY]

    def pr(self, **kwargs):
        base = {"number": 1, "author": {"login": "alice"}, "createdAt": None,
                "mergedAt": None, "closedAt": None}
        base.update(kwargs)
        return base

    def analyse(self, mirror, pr, now=9999, gap=7200):
        return conflict_stats.analyse_pr(mirror, self.HISTORY, self.TIMES, pr, now, gap)

    def test_a_never_conflicting_pr_yields_nothing(self):
        mirror = self.FakeMirror([("h1", 1000)], {})
        episodes, handling = self.analyse(mirror, self.pr())
        self.assertEqual(episodes, [])
        self.assertEqual(handling, "")

    def test_onset_is_the_first_main_commit_that_breaks_the_merge(self):
        # Head h1 is current from t=1000 until the push at t=1650; main commit 5
        # (t=1500) is the first that conflicts with it.
        mirror = self.FakeMirror([("h1", 1000), ("h2", 1650)], {"h1": 5})
        episodes, _ = self.analyse(mirror, self.pr())
        self.assertEqual(len(episodes), 1)
        self.assertEqual(episodes[0]["onset"], 1500)
        self.assertEqual(episodes[0]["resolved"], 1650)
        self.assertEqual(episodes[0]["outcome"], "push")

    def test_binary_search_costs_a_handful_of_merges_not_one_per_commit(self):
        mirror = self.FakeMirror([("h1", 1000), ("h2", 3000)], {"h1": 5})
        self.analyse(mirror, self.pr())
        self.assertLess(mirror.merges, len(self.HISTORY))

    def test_an_epoch_that_ends_clean_is_reported_clean(self):
        # Monotonicity is an assumption, not a theorem: check the last base first.
        mirror = self.FakeMirror([("h1", 1000), ("h2", 3000)], {})
        episodes, _ = self.analyse(mirror, self.pr())
        self.assertEqual(episodes, [])

    def test_a_still_open_conflict_is_measured_to_now(self):
        mirror = self.FakeMirror([("h1", 1000)], {"h1": 5})
        episodes, _ = self.analyse(mirror, self.pr(), now=9999)
        self.assertEqual(episodes[0]["outcome"], "still-open")
        self.assertEqual(episodes[0]["resolved"], 9999)
        self.assertIsNone(episodes[0]["continuation"])

    def test_a_conflict_that_ends_at_the_merge_is_labelled_merged(self):
        mirror = self.FakeMirror([("h1", 1000)], {"h1": 5})
        episodes, _ = self.analyse(mirror, self.pr(mergedAt="2026-01-01T00:00:00Z"))
        self.assertEqual(episodes[0]["outcome"], "merged")

    def test_a_quick_follow_up_push_counts_as_a_continuation(self):
        mirror = self.FakeMirror([("h0", 900), ("h1", 1000), ("h2", 1600)], {"h1": 5})
        episodes, _ = self.analyse(mirror, self.pr(), gap=7200)
        [episode] = [e for e in episodes if e["outcome"] == "push"]
        self.assertTrue(episode["continuation"])

    def test_a_push_long_after_the_last_one_counts_as_a_return(self):
        mirror = self.FakeMirror([("h0", 900), ("h1", 1000), ("h2", 1600)], {"h1": 5})
        episodes, _ = self.analyse(mirror, self.pr(), gap=60)
        [episode] = [e for e in episodes if e["outcome"] == "push"]
        self.assertFalse(episode["continuation"])

    def test_a_rebased_pr_is_flagged_as_unmeasurable(self):
        # Every commit rewritten to one timestamp: the pre-rebase window is gone.
        mirror = self.FakeMirror([("h1", 1500), ("h2", 1500)], {})
        _, handling = self.analyse(mirror, self.pr())
        self.assertEqual(handling, "rewritten")

    def test_conflicts_before_the_pr_existed_are_not_counted(self):
        # A branch's commits routinely predate the PR proposing them; a PR cannot
        # conflict before it was opened.
        mirror = self.FakeMirror([("h1", 1000)], {"h1": 0})
        episodes, _ = self.analyse(mirror, self.pr(createdAt="1970-01-01T00:28:20Z"))
        # created at t=1700, so onset cannot be earlier than main commit index 7.
        self.assertTrue(all(e["onset"] >= 1700 for e in episodes), episodes)

    def test_exhaustive_finds_a_conflict_an_epoch_ends_clean_after(self):
        class Transient(self.FakeMirror):
            def conflicts(self, base_sha, head_sha):
                self.merges += 1
                return 5 <= int(base_sha) <= 9     # clean again from 10 onwards
        mirror = Transient([("h1", 1000)], {})
        self.assertIsNone(conflict_stats.first_conflicting(
            mirror, self.HISTORY, 0, 20, "h1"))
        self.assertEqual(conflict_stats.first_conflicting(
            mirror, self.HISTORY, 0, 20, "h1", exhaustive=True), 5)

    def test_a_pr_with_no_fetchable_head_is_skipped_not_guessed(self):
        mirror = self.FakeMirror([], {})
        self.assertEqual(self.analyse(mirror, self.pr()), ([], "skipped"))


class ReplaySummary(unittest.TestCase):
    def episodes(self):
        return [
            {"pr": 1, "author": "alice", "onset": 0, "resolved": 3600,
             "seconds": 3600, "outcome": "push", "continuation": True},
            {"pr": 2, "author": "alice", "onset": 0, "resolved": 200000,
             "seconds": 200000, "outcome": "push", "continuation": False},
            {"pr": 3, "author": "bob", "onset": 0, "resolved": 500000,
             "seconds": 500000, "outcome": "still-open", "continuation": None},
        ]

    def test_reports_the_over_24h_tail_and_the_session_split(self):
        lines = "\n".join(conflict_stats.summarise(
            self.episodes(), unmeasured={"rewritten": 4, "skipped": 2}, total_prs=99))
        self.assertIn("3 conflict episode(s) across 3 of 99 PR(s)", lines)
        self.assertIn("4 PR(s) had their history rewritten", lines)
        self.assertIn("2 had no replayable commits", lines)
        self.assertIn("1/2 took over 24h", lines)
        self.assertIn("1 while the author was already working the PR, 1 on a later return", lines)
        self.assertIn("still conflicting", lines)


if __name__ == "__main__":
    unittest.main()
