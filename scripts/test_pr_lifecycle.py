#!/usr/bin/env python3
"""Hermetic tests for scripts/pr_lifecycle.py, the shared lifecycle rules."""

from __future__ import annotations

import unittest
from datetime import datetime, timedelta, timezone

import pr_lifecycle as lc

UTC = timezone.utc
NOW = datetime(2026, 8, 25, 12, tzinfo=UTC)


def iso(when):
    return when.strftime("%Y-%m-%dT%H:%M:%SZ")


def pr(events, *, state="OPEN", labels=None, merged=None):
    return {
        "state": state,
        "merged_at": iso(merged) if merged else None,
        "closed_at": iso(merged) if merged else None,
        "labels": labels if labels is not None else ([events[-1][1]] if events else []),
        "labeled_events": [{"created_at": iso(at), "label": name} for at, name in events],
    }


class JoiningTests(unittest.TestCase):
    def test_author_action_siblings_are_one_spell(self):
        """The author reads a build log for one and review threads for the other,
        but the ball is in their court either way."""
        spells = list(lc.episodes(pr([
            (NOW - timedelta(hours=20), "ci-failed"),
            (NOW - timedelta(hours=1), "awaiting-author"),
        ]), NOW))
        self.assertEqual(len(spells), 1)
        self.assertEqual(spells[0][1], NOW - timedelta(hours=20))

    def test_review_siblings_are_one_spell(self):
        spells = list(lc.episodes(pr([
            (NOW - timedelta(hours=12), "awaiting-review"),
            (NOW - timedelta(hours=2), "review-in-progress"),
        ]), NOW))
        self.assertEqual(len(spells), 1)

    def test_anything_else_starts_a_fresh_spell(self):
        spells = list(lc.episodes(pr([
            (NOW - timedelta(hours=30), "awaiting-author"),
            (NOW - timedelta(hours=3), "awaiting-CI"),
        ]), NOW))
        self.assertEqual([s[0] for s in spells], ["author-action", "awaiting-CI"])

    def test_a_closed_pr_s_last_spell_ends_at_the_close(self):
        merged = NOW - timedelta(hours=1)
        spells = list(lc.episodes(
            pr([(NOW - timedelta(hours=5), "ready-to-merge")], state="MERGED", merged=merged), NOW))
        self.assertEqual(spells[-1][2], merged)

    def test_an_open_pr_s_last_spell_is_still_running(self):
        spells = list(lc.episodes(pr([(NOW - timedelta(hours=5), "awaiting-review")]), NOW))
        self.assertIsNone(spells[-1][2])


class CurrentStageTests(unittest.TestCase):
    def test_from_labels_not_from_history(self):
        item = pr([(NOW - timedelta(hours=5), "awaiting-review")], labels=[])
        self.assertIsNone(lc.current_stage(item))

    def test_a_single_lifecycle_label_wins(self):
        item = pr([], labels=["roadmap:algebra", "awaiting-review"])
        self.assertEqual(lc.current_stage(item), "awaiting-review")

    def test_two_lifecycle_labels_is_no_answer(self):
        """The pipeline keeps one at a time, so two means something is wrong and
        guessing between them would invent a fact."""
        item = pr([], labels=["awaiting-review", "ci-failed"])
        self.assertIsNone(lc.current_stage(item))


class AgreementTests(unittest.TestCase):
    def test_author_episode_start_matches_the_shared_spell(self):
        item = pr([
            (NOW - timedelta(hours=20), "ci-failed"),
            (NOW - timedelta(hours=1), "awaiting-author"),
        ])
        spells = list(lc.episodes(item, NOW))
        self.assertEqual(lc.author_episode_start(item), spells[-1][1])

    def test_review_cycle_start_matches_the_shared_spell(self):
        item = pr([
            (NOW - timedelta(hours=12), "awaiting-review"),
            (NOW - timedelta(hours=2), "review-in-progress"),
        ])
        self.assertEqual(lc.review_cycle_starts(item)[-1], list(lc.episodes(item, NOW))[-1][1])


class SeparationTests(unittest.TestCase):
    """Waiting spells and per-label rates are different questions.

    Using one decomposition for both meant a ci-failed to awaiting-author swap
    recorded no dwell for ci-failed at all, and dated awaiting-author's arrival
    nineteen hours before it happened. The waiting time was right and every rate
    was wrong.
    """

    def swap(self):
        return pr([
            (NOW - timedelta(hours=20), "ci-failed"),
            (NOW - timedelta(hours=1), "awaiting-author"),
        ])

    def test_atomic_intervals_keep_each_label_separate(self):
        got = [(label, end) for label, _, end in lc.label_intervals(self.swap(), NOW)]
        self.assertEqual([label for label, _ in got], ["ci-failed", "awaiting-author"])
        self.assertIsNone(got[-1][1])

    def test_the_first_label_records_its_own_dwell(self):
        first = next(iter(lc.label_intervals(self.swap(), NOW)))
        self.assertAlmostEqual((first[2] - first[1]).total_seconds() / 3600, 19.0, places=3)

    def test_the_spell_is_one_group_and_keeps_the_whole_wait(self):
        spells = list(lc.episodes(self.swap(), NOW))
        self.assertEqual([g for g, _, _ in spells], ["author-action"])
        self.assertEqual(spells[0][1], NOW - timedelta(hours=20))

    def test_episodes_yield_a_group_not_a_label(self):
        """The old version claimed to yield the starting label and yielded the
        final one, which silently decided which label got the duration."""
        groups = {g for g, _, _ in lc.episodes(self.swap(), NOW)}
        self.assertEqual(groups, {"author-action"})
        self.assertNotIn("ci-failed", groups)


class CensoringTests(unittest.TestCase):
    def test_a_removed_label_is_not_still_running(self):
        """Only additions are recorded, so a label taken off without another
        arriving would otherwise look like it was still in force."""
        item = pr([(NOW - timedelta(hours=5), "awaiting-review")], labels=[])
        self.assertEqual([i for i in lc.label_intervals(item, NOW)], [])
        self.assertIsNone(lc.waiting_since(item, NOW))

    def test_a_label_still_present_is_running(self):
        item = pr([(NOW - timedelta(hours=5), "awaiting-review")])
        self.assertIsNone(list(lc.label_intervals(item, NOW))[-1][2])


class DeliberateDifferenceTests(unittest.TestCase):
    def test_review_cycles_and_waiting_spells_count_differently(self):
        """A pull request that reached ready-to-merge and came back has waited
        twice while having been reviewed once. Both answers are correct; the
        point is that the difference is intended and pinned."""
        item = pr([
            (NOW - timedelta(hours=9), "awaiting-review"),
            (NOW - timedelta(hours=6), "ready-to-merge"),
            (NOW - timedelta(hours=3), "awaiting-review"),
        ])
        self.assertEqual(len(lc.review_cycle_starts(item)), 1)
        self.assertEqual(sum(1 for g, _, _ in lc.episodes(item, NOW) if g == "review"), 2)


if __name__ == "__main__":
    unittest.main()
