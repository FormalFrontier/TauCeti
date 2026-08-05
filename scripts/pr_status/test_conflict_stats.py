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

    HISTORY = [(str(i), 1000 + 100 * i, f"feat: commit {i}") for i in range(20)]
    TIMES = [when for _, when, _ in HISTORY]

    def pr(self, **kwargs):
        base = {"number": 1, "author": {"login": "alice"}, "createdAt": None,
                "mergedAt": None, "closedAt": None}
        base.update(kwargs)
        return base

    def analyse(self, mirror, pr, now=9999, gap=7200, actors=None, window=0):
        """Replay, then attribute. `actors` maps head sha -> github login; by
        default every head is the PR's own author."""
        rows, handling, epochs = conflict_stats.analyse_pr(
            mirror, self.HISTORY, self.TIMES, pr, now, gap, push_window=window)
        author = (pr.get("author") or {}).get("login") or ""
        if actors is None:
            actors = {sha: author for sha, _ in epochs}
        conflict_stats.attribute(rows, epochs, actors, author, gap)
        return rows, handling

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
        self.assertIsNone(episodes[0]["session"])

    def test_a_conflict_that_ends_at_the_merge_is_labelled_merged(self):
        mirror = self.FakeMirror([("h1", 1000)], {"h1": 5})
        episodes, _ = self.analyse(mirror, self.pr(mergedAt="2026-01-01T00:00:00Z"))
        self.assertEqual(episodes[0]["outcome"], "merged")

    def test_a_quick_follow_up_push_counts_as_a_continuation(self):
        mirror = self.FakeMirror([("h0", 900), ("h1", 1000), ("h2", 1600)], {"h1": 5})
        episodes, _ = self.analyse(mirror, self.pr(), gap=7200)
        [episode] = [e for e in episodes if e["outcome"] == "push"]
        self.assertEqual(episode["session"], conflict_stats.CONTINUATION)

    def test_a_push_long_after_the_last_one_counts_as_a_return(self):
        mirror = self.FakeMirror([("h0", 900), ("h1", 1000), ("h2", 1600)], {"h1": 5})
        episodes, _ = self.analyse(mirror, self.pr(), gap=60)
        [episode] = [e for e in episodes if e["outcome"] == "push"]
        self.assertEqual(episode["session"], conflict_stats.RETURN)

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

    def test_a_pr_born_conflicting_is_detected_and_dated_to_its_opening(self):
        # The base in effect when the PR opened already conflicts. Replaying only
        # main commits strictly after the opening never tested it, so the whole
        # episode was invisible; and it must date to the opening, not to the older
        # main commit that happened to be current then.
        mirror = self.FakeMirror([("h1", 1550)], {"h1": 0})
        episodes, _ = self.analyse(mirror, self.pr(createdAt="1970-01-01T00:25:50Z"))
        self.assertEqual(len(episodes), 1)
        self.assertEqual(episodes[0]["onset"], 1550)

    def test_a_conflict_with_no_later_main_commit_is_still_found(self):
        # Window contains no main commit at all: there is still a base to conflict
        # with, and the old code searched an empty range and found nothing.
        mirror = self.FakeMirror([("h1", 2905)], {"h1": 0})
        episodes, _ = self.analyse(mirror, self.pr(), now=2950)
        self.assertEqual(len(episodes), 1)
        self.assertEqual(episodes[0]["outcome"], "still-open")

    def test_consecutive_conflicting_heads_are_one_episode(self):
        # Commits pushed together look like separate heads here. Calling each
        # following one a resolution fragmented a single continuous conflict into a
        # string of falsely resolved episodes.
        mirror = self.FakeMirror(
            [("h1", 1000), ("h2", 1650), ("h3", 1660)], {"h1": 5, "h2": 0, "h3": 0})
        episodes, _ = self.analyse(mirror, self.pr())
        self.assertEqual(len(episodes), 1)
        self.assertEqual(episodes[0]["onset"], 1500)
        self.assertEqual(episodes[0]["outcome"], "still-open")

    def test_a_clean_successor_head_is_what_ends_an_episode(self):
        mirror = self.FakeMirror(
            [("h1", 1000), ("h2", 1650), ("h3", 1900)], {"h1": 5, "h2": 0})
        episodes, _ = self.analyse(mirror, self.pr())
        self.assertEqual(len(episodes), 1)
        self.assertEqual(episodes[0]["resolved"], 1900)
        self.assertEqual(episodes[0]["outcome"], "push")

    def test_the_prs_own_landing_commit_is_not_a_base(self):
        # A squash-merge of this PR conflicts with its own head by construction,
        # which made the merge look like the cause of the conflict.
        history = self.HISTORY[:10] + [("10", 2000, "feat: do a thing (#1)")] + self.HISTORY[11:]
        times = [when for _, when, _ in history]
        mirror = self.FakeMirror([("h1", 1000)], {"h1": 10})
        episodes, _, _ = conflict_stats.analyse_pr(
            mirror, history, times, self.pr(mergedAt="1970-01-01T00:33:20Z"), 9999, 7200,
            push_window=0)
        self.assertEqual(episodes, [])

    def test_a_resolution_by_someone_else_is_not_credited_to_the_author(self):
        # git records a committer string, not a GitHub account. Without the API a
        # maintainer or bot pushing the fix was silently scored as the author
        # returning to their own PR.
        mirror = self.FakeMirror([("h1", 1000), ("h2", 1650)], {"h1": 5})
        episodes, _ = self.analyse(mirror, self.pr(), actors={"h1": "alice", "h2": "carol"})
        self.assertEqual(episodes[0]["session"], conflict_stats.OTHER_ACTOR)
        self.assertEqual(episodes[0]["resolver"], "carol")

    def test_an_unnameable_actor_is_left_unattributed(self):
        mirror = self.FakeMirror([("h1", 1000), ("h2", 1650)], {"h1": 5})
        episodes, _ = self.analyse(mirror, self.pr(), actors={})
        self.assertEqual(episodes[0]["session"], conflict_stats.UNATTRIBUTED)
        self.assertIsNone(episodes[0]["resolver"])

    def test_the_gap_is_measured_against_the_same_actors_previous_push(self):
        # bob pushing in between must not disguise alice's return as a continuation.
        # alice pushed at 1100, bob at 2400, alice again at 2500. Against bob's
        # push the gap is 100s (a continuation); against alice's own it is 1400s.
        mirror = self.FakeMirror(
            [("h0", 1100), ("h1", 2400), ("h2", 2500)], {"h1": 5})
        episodes, _ = self.analyse(
            mirror, self.pr(), gap=600,
            actors={"h0": "alice", "h1": "bob", "h2": "alice"})
        [row] = [e for e in episodes if e["outcome"] == "push"]
        self.assertEqual(row["session"], conflict_stats.RETURN)

    def test_commits_within_the_push_window_are_one_head(self):
        # Only the last commit of a push was ever the branch head; an intermediate
        # one that conflicts must not invent an episode.
        mirror = self.FakeMirror([("h1", 1000), ("h2", 1010)], {"h1": 0})
        episodes, _ = self.analyse(mirror, self.pr(), window=120)
        self.assertEqual(episodes, [])
        # With grouping off, the intermediate commit is treated as a real head.
        mirror = self.FakeMirror([("h1", 1000), ("h2", 1010)], {"h1": 0})
        episodes, _ = self.analyse(mirror, self.pr(), window=0)
        self.assertEqual(len(episodes), 1)

    def test_a_pr_with_no_fetchable_head_is_skipped_not_guessed(self):
        mirror = self.FakeMirror([], {})
        self.assertEqual(self.analyse(mirror, self.pr()), ([], "skipped"))


class ReplaySummary(unittest.TestCase):
    def episodes(self):
        return [
            {"pr": 1, "author": "alice", "onset": 0, "resolved": 3600, "seconds": 3600,
             "outcome": "push", "session": conflict_stats.CONTINUATION, "resolver": "alice"},
            {"pr": 2, "author": "alice", "onset": 0, "resolved": 200000, "seconds": 200000,
             "outcome": "push", "session": conflict_stats.RETURN, "resolver": "alice"},
            {"pr": 3, "author": "bob", "onset": 0, "resolved": 500000, "seconds": 500000,
             "outcome": "still-open", "session": None, "resolver": None},
            {"pr": 4, "author": "bob", "onset": 0, "resolved": 900, "seconds": 900,
             "outcome": "push", "session": conflict_stats.OTHER_ACTOR, "resolver": "carol"},
        ]

    def test_reports_the_over_24h_tail_and_the_session_split(self):
        lines = "\n".join(conflict_stats.summarise(
            self.episodes(), unmeasured={"rewritten": 4, "skipped": 2}, total_prs=99))
        self.assertIn("4 conflict episode(s) across 4 of 99 PR(s)", lines)
        self.assertIn("4 PR(s) had their history rewritten", lines)
        self.assertIn("2 had no replayable commits", lines)
        self.assertIn("1/3 took over 24h", lines)
        self.assertIn("1 by the PR's author, already pushing to it", lines)
        self.assertIn("1 by the PR's author, returning after a gap", lines)
        self.assertIn("1 by someone other than the PR's author", lines)
        self.assertIn("still conflicting", lines)


if __name__ == "__main__":
    unittest.main()
