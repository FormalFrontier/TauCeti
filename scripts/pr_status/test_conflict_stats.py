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
        """Replay through the push ledger. `actors` maps head sha -> github login;
        by default every head was pushed by the PR's own author."""
        author = (pr.get("author") or {}).get("login") or ""
        heads = mirror.pr_heads(pr["number"])
        if actors is None:
            actors = {sha: author for sha, _ in heads}
        ledger = [{"sha": sha, "actor": actors[sha], "when": when,
                   "owner": "o", "branch": "b"}
                  for sha, when in heads if sha in actors]
        pr = dict(pr, headRefName="b", headRepositoryOwner={"login": "o"})
        index = conflict_stats.ledger_index(ledger)
        pr["_pushes"] = [row for row in index.get(("o", "b"), [])]
        rows, handling, _, _ = conflict_stats.analyse_pr(
            mirror, self.HISTORY, self.TIMES, pr, now, gap, push_window=window,
            index=index, available={r["sha"] for r in ledger})
        return rows, handling

    def analyse_pushes(self, mirror, pr, pushes, gap=7200, now=9999):
        """Replay a ledger given as (sha, when, actor) OCCURRENCES, so a head that
        was returned to can carry a different actor each time it was pushed."""
        ledger = [{"sha": sha, "actor": actor, "when": when,
                   "owner": "o", "branch": "b"} for sha, when, actor in pushes]
        pr = dict(pr, headRefName="b", headRepositoryOwner={"login": "o"})
        index = conflict_stats.ledger_index(ledger)
        pr["_pushes"] = index[("o", "b")]
        rows, _, _, _ = conflict_stats.analyse_pr(
            mirror, self.HISTORY, self.TIMES, pr, now, gap, push_window=0,
            index=index, available={sha for sha, _, _ in pushes})
        return rows

    def test_a_never_conflicting_pr_yields_nothing(self):
        mirror = self.FakeMirror([("h1", 1000)], {})
        episodes, handling = self.analyse(mirror, self.pr())
        self.assertEqual(episodes, [])
        self.assertEqual(handling, "recorded")

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

    def test_ledger_coverage_is_reported_as_such(self):
        mirror = self.FakeMirror([("h1", 1500), ("h2", 1600)], {})
        _, handling = self.analyse(mirror, self.pr())
        self.assertEqual(handling, "recorded")

    def test_only_ledger_commits_count_as_heads(self):
        # A commit that never appears in the ledger was never a head, so an
        # intermediate one that conflicts cannot invent an episode.
        mirror = self.FakeMirror([("h1", 1000), ("h2", 1010)], {"h1": 0})
        episodes, handling = self.analyse(mirror, self.pr(), actors={"h2": "alice"})
        self.assertEqual(handling, "recorded")
        self.assertEqual(episodes, [])

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

    def test_current_state_decides_the_outcome_not_closedat(self):
        # Reading `closedAt` first censored an open PR out of the live tail this
        # tool exists to report. State decides; a stale or unexpected `closedAt` on
        # an open PR must not override it.
        mirror = self.FakeMirror([("h1", 1000)], {"h1": 5})
        pr = self.pr(closedAt="1970-01-01T00:30:00Z", state="OPEN")
        episodes, _ = self.analyse(mirror, pr)
        self.assertEqual(episodes[0]["outcome"], "still-open")

    def test_a_genuinely_closed_pr_is_closed(self):
        mirror = self.FakeMirror([("h1", 1000)], {"h1": 5})
        episodes, _ = self.analyse(
            mirror, self.pr(closedAt="1970-01-01T00:30:00Z", state="CLOSED"))
        self.assertEqual(episodes[0]["outcome"], "closed")

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
        episodes, _, _, _ = conflict_stats.analyse_pr(
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
        # No ledger coverage at all: heads inferred from commits, actor unknown.
        rows, handling, _, _ = conflict_stats.analyse_pr(
            mirror, self.HISTORY, self.TIMES, self.pr(), 9999, 7200, push_window=0)
        self.assertEqual(handling, "inferred")
        episodes = rows
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

    def test_a_returned_to_head_does_not_invent_a_push_by_its_new_actor(self):
        # A -> B -> A, where carol pushed the first A and alice the second. Keying
        # actors by sha gave BOTH occurrences alice, so searching back for her
        # previous push found carol's, and alice's return read as a continuation
        # of a session she had never started.
        mirror = self.FakeMirror([], {"B": 5})
        episodes = self.analyse_pushes(
            mirror, self.pr(), gap=3600,
            pushes=[("A", 1000, "carol"), ("B", 1650, "bob"), ("A", 2500, "alice")])
        [row] = [e for e in episodes if e["outcome"] == "push"]
        self.assertEqual(row["resolver"], "alice")
        self.assertIsNone(row["gap"])
        self.assertEqual(row["session"], conflict_stats.RETURN)

    def test_an_earlier_occurrence_of_a_head_keeps_its_own_actor(self):
        # The same conflation the other way round: alice pushed A and resolved the
        # conflict, and carol's later force-push back to A overwrote the actor on
        # alice's push, crediting the fix to someone who had not made it yet.
        mirror = self.FakeMirror([], {"X": 5})
        episodes = self.analyse_pushes(
            mirror, self.pr(),
            pushes=[("X", 900, "alice"), ("A", 1650, "alice"),
                    ("Y", 2000, "carol"), ("A", 2500, "carol")])
        [row] = [e for e in episodes if e["outcome"] == "push"]
        self.assertEqual(row["resolver"], "alice")
        self.assertEqual(row["session"], conflict_stats.CONTINUATION)

    def test_the_push_window_groups_commits_when_inferring(self):
        # Without ledger coverage we fall back to commit dates. Commits written
        # seconds apart travelled in one push, so an intermediate one that
        # conflicts must not invent an episode.
        def run(window):
            mirror = self.FakeMirror([("h1", 1000), ("h2", 1010)], {"h1": 0})
            rows, handling, _, _ = conflict_stats.analyse_pr(
                mirror, self.HISTORY, self.TIMES, self.pr(), 9999, 7200,
                push_window=window)
            self.assertEqual(handling, "inferred")
            return rows
        self.assertEqual(run(120), [])
        self.assertEqual(len(run(0)), 1)

    def test_partial_ledger_coverage_is_not_reported_as_full(self):
        # One matching head used to mark the whole PR recorded, silently dropping
        # every head that could not be fetched and truncating its episodes.
        mirror = self.FakeMirror([("h1", 1000), ("h2", 1650)], {"h1": 5})
        ledger = [{"sha": sha, "actor": "alice", "when": when,
                   "owner": "o", "branch": "b"}
                  for sha, when in [("h1", 1000), ("h2", 1650)]]
        pr = dict(self.pr(), headRefName="b", headRepositoryOwner={"login": "o"})
        pr["_pushes"] = [("h1", 1000, "alice"), ("h2", 1650, "alice")]
        _, handling, _, _ = conflict_stats.analyse_pr(
            mirror, self.HISTORY, self.TIMES, pr, 9999, 7200,
            index=conflict_stats.ledger_index(ledger), available={"h1"})
        self.assertEqual(handling, "partial")

    def test_branch_reuse_does_not_borrow_another_prs_pushes(self):
        # `fix/typo` belongs to a dozen PRs over time; only the pushes inside this
        # PR's own lifetime are its own.
        ledger = [
            {"sha": "old", "actor": "a", "when": 500, "owner": "o", "branch": "b"},
            {"sha": "mine", "actor": "a", "when": 1500, "owner": "o", "branch": "b"},
            {"sha": "later", "actor": "a", "when": 9000, "owner": "o", "branch": "b"},
        ]
        pr = {"headRefName": "b", "headRepositoryOwner": {"login": "o"}}
        pushes = conflict_stats.pr_pushes(pr, conflict_stats.ledger_index(ledger), 1000, 2000)
        self.assertEqual(pushes, [("mine", 1500, "a")])

    def test_a_pr_with_no_fetchable_head_is_skipped_not_guessed(self):
        mirror = self.FakeMirror([], {})
        self.assertEqual(self.analyse(mirror, self.pr()), ([], "skipped"))


class LedgerIndex(unittest.TestCase):
    """Which repeats of a head are transitions and which are noise."""

    def rows(self, *items):
        return [{"sha": sha, "actor": "a", "when": when, "owner": "o", "branch": "b"}
                for sha, when in items]

    def test_adjacent_repeats_collapse_to_the_earliest(self):
        # A re-run or a reopen re-reports the current head; neither moved it.
        index = conflict_stats.ledger_index(self.rows(("A", 100), ("A", 200), ("B", 300)))
        self.assertEqual([row[0] for row in index[("o", "b")]], ["A", "B"])
        self.assertEqual(index[("o", "b")][0][1], 100)

    def test_a_head_returned_to_later_is_kept(self):
        # A -> B -> A is a real force-push back; the second A can be the push that
        # resolved the conflict, and deduplicating by sha discarded it.
        index = conflict_stats.ledger_index(self.rows(("A", 100), ("B", 200), ("A", 300)))
        self.assertEqual([row[0] for row in index[("o", "b")]], ["A", "B", "A"])

    def test_the_same_sha_on_two_branches_stays_separate(self):
        rows = self.rows(("A", 100))
        rows.append({"sha": "A", "actor": "a", "when": 150, "owner": "o", "branch": "other"})
        index = conflict_stats.ledger_index(rows)
        self.assertEqual(len(index[("o", "b")]), 1)
        self.assertEqual(len(index[("o", "other")]), 1)


class ClosedIntervals(unittest.TestCase):
    """A conflict cannot be unresolved while the PR is closed: nobody could merge it."""

    def episode(self, onset, resolved):
        return {"pr": 1, "onset": onset, "resolved": resolved,
                "seconds": resolved - onset, "closed_seconds": 0, "outcome": "push"}

    def test_no_intervals_changes_nothing(self):
        rows = [self.episode(0, 100)]
        self.assertEqual(conflict_stats.clip_episodes(rows, []), rows)

    def test_time_spent_closed_is_subtracted(self):
        rows = conflict_stats.clip_episodes([self.episode(0, 100)], [(20, 50)])
        self.assertEqual(rows[0]["seconds"], 70)

    def test_the_discount_is_recorded_rather_than_silently_applied(self):
        # `seconds` no longer equals `resolved - onset` once time is taken out, so
        # the row has to say how much, or the JSON contradicts itself.
        rows = conflict_stats.clip_episodes([self.episode(0, 100)], [(20, 50)])
        row = rows[0]
        self.assertEqual(row["closed_seconds"], 30)
        self.assertEqual(row["seconds"], row["resolved"] - row["onset"]
                         - row["closed_seconds"])

    def test_an_episode_entirely_inside_a_closed_interval_is_dropped(self):
        self.assertEqual(conflict_stats.clip_episodes([self.episode(30, 40)], [(20, 50)]), [])

    def test_an_interval_outside_the_episode_is_ignored(self):
        rows = conflict_stats.clip_episodes([self.episode(0, 100)], [(200, 300)])
        self.assertEqual(rows[0]["seconds"], 100)

    def test_a_pulse_of_brief_closures_stays_one_episode(self):
        # What close/reopen actually looks like here: the review bot shutting a PR
        # and opening it again a second later, fifteen times (#1908). Splitting the
        # episode at each boundary would report fifteen abandonments that never
        # happened; the conflict was continuous and the closures cost 15 seconds.
        pulses = [(10 * i, 10 * i + 1) for i in range(1, 16)]
        rows = conflict_stats.clip_episodes([self.episode(0, 1000)], pulses)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["outcome"], "push")
        self.assertEqual(rows[0]["closed_seconds"], 15)
        self.assertEqual(rows[0]["seconds"], 985)


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
            self.episodes(), handled={"recorded": 40, "inferred": 4, "skipped": 2},
            total_prs=99))
        self.assertIn("4 conflict episode(s) across 4 of 99 PR(s)", lines)
        self.assertIn("40 PR(s) fully recorded", lines)
        self.assertIn("4 inferred from commit dates", lines)
        self.assertIn("2 with no replayable commits", lines)
        self.assertIn("1/3 took over 24h", lines)
        self.assertIn("1 by the PR's author, already pushing to it", lines)
        self.assertIn("1 by the PR's author, returning after a gap", lines)
        self.assertIn("1 by someone other than the PR's author", lines)
        self.assertIn("still conflicting", lines)


if __name__ == "__main__":
    unittest.main()
