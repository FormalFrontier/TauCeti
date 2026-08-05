#!/usr/bin/env python3
"""Unit tests for the merge-conflict sink (conflicts) and the replay (conflict_stats).

Pure logic only: GitHub reads/writes and `git` are stubbed, so these run with no
network, no `gh`, and no repository. Run with:  python3 test_conflicts.py
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import conflict_stats  # noqa: E402
import conflicts  # noqa: E402
import core  # noqa: E402


class Marker(unittest.TestCase):
    def test_round_trips_an_open_episode(self):
        body = conflicts.conflict_body(1_700_000_000)
        self.assertEqual(conflicts.parse_marker(body), {"onset": 1_700_000_000})

    def test_round_trips_a_resolved_episode(self):
        body = conflicts.resolved_body(1_700_000_000, 1_700_086_400)
        self.assertEqual(conflicts.parse_marker(body),
                         {"onset": 1_700_000_000, "resolved": 1_700_086_400})

    def test_resolved_body_states_the_duration_it_recorded(self):
        body = conflicts.resolved_body(1_700_000_000, 1_700_000_000 + 3 * 3600 + 720)
        self.assertIn("3h 12m", body)

    def test_a_body_without_a_marker_reads_as_absent(self):
        self.assertIsNone(conflicts.parse_marker("just a review comment"))
        self.assertIsNone(conflicts.parse_marker(""))
        self.assertIsNone(conflicts.parse_marker(None))

    def test_malformed_or_typeless_markers_are_ignored(self):
        self.assertIsNone(conflicts.parse_marker("<!--tauceti-conflict:v1 {nope}-->"))
        self.assertIsNone(conflicts.parse_marker('<!--tauceti-conflict:v1 {"onset":"soon"}-->'))
        self.assertIsNone(conflicts.parse_marker('<!--tauceti-conflict:v1 [1]-->'))


class ConflictComments(unittest.TestCase):
    def setUp(self):
        self._saved = core.trusted_comments

    def tearDown(self):
        core.trusted_comments = self._saved

    def stub(self, *comments):
        core.trusted_comments = lambda pr: list(comments)

    def comment(self, cid, onset, resolved=None):
        body = (conflicts.resolved_body(onset, resolved) if resolved
                else conflicts.conflict_body(onset))
        return {"id": cid, "body": body, "updated": "2026-01-01T00:00:00Z"}

    def test_orders_episodes_oldest_first(self):
        self.stub(self.comment(20, 300), self.comment(10, 100, 200))
        found = conflicts.conflict_comments("1")
        self.assertEqual([c["marker"]["onset"] for c in found], [100, 300])
        self.assertEqual([c["resolved"] for c in found], [True, False])

    def test_ignores_unrelated_comments(self):
        self.stub({"id": 1, "body": "<!--tauceti-scoreboard--> nope", "updated": "x"})
        self.assertEqual(conflicts.conflict_comments("1"), [])


class ReconcilePR(unittest.TestCase):
    """The comment state machine: opened / ongoing / resolved / clear / parked."""

    NOW = 1_700_100_000

    def setUp(self):
        self._comments = core.trusted_comments
        self._post = conflicts.post_comment
        self._edit = conflicts.edit_comment
        self.posted, self.edited = [], []
        conflicts.post_comment = lambda pr, body: self.posted.append((pr, body))
        conflicts.edit_comment = lambda cid, body: self.edited.append((cid, body))

    def tearDown(self):
        core.trusted_comments = self._comments
        conflicts.post_comment = self._post
        conflicts.edit_comment = self._edit

    def history(self, *comments):
        core.trusted_comments = lambda pr: list(comments)

    def open_episode(self, cid, onset):
        return {"id": cid, "body": conflicts.conflict_body(onset), "updated": "u"}

    def closed_episode(self, cid, onset, resolved):
        return {"id": cid, "body": conflicts.resolved_body(onset, resolved), "updated": "u"}

    def test_first_conflict_posts_exactly_one_comment(self):
        self.history()
        self.assertEqual(
            conflicts.reconcile_pr("7", True, now=self.NOW), "opened")
        self.assertEqual(len(self.posted), 1)
        self.assertEqual(conflicts.parse_marker(self.posted[0][1]), {"onset": self.NOW})

    def test_an_ongoing_conflict_is_never_touched_again(self):
        self.history(self.open_episode(11, self.NOW - 7200))
        self.assertEqual(conflicts.reconcile_pr("7", True, now=self.NOW), "ongoing")
        self.assertEqual((self.posted, self.edited), ([], []))

    def test_resolution_edits_the_live_comment_and_records_both_times(self):
        onset = self.NOW - 5000
        self.history(self.open_episode(11, onset))
        self.assertEqual(conflicts.reconcile_pr("7", False, now=self.NOW), "resolved")
        self.assertEqual(self.posted, [])
        self.assertEqual(len(self.edited), 1)
        cid, body = self.edited[0]
        self.assertEqual(cid, 11)
        self.assertEqual(conflicts.parse_marker(body), {"onset": onset, "resolved": self.NOW})

    def test_a_clean_pr_with_no_history_does_nothing(self):
        self.history()
        self.assertEqual(conflicts.reconcile_pr("7", False, now=self.NOW), "clear")
        self.assertEqual((self.posted, self.edited), ([], []))

    def test_a_clean_pr_whose_episode_is_already_closed_does_nothing(self):
        self.history(self.closed_episode(11, 100, 200))
        self.assertEqual(conflicts.reconcile_pr("7", False, now=self.NOW), "clear")
        self.assertEqual((self.posted, self.edited), ([], []))

    def test_a_recurrence_posts_a_fresh_comment(self):
        # Editing the buried resolved comment would notify nobody, so a second
        # conflict has to be a new comment.
        self.history(self.closed_episode(11, 100, 200))
        self.assertEqual(conflicts.reconcile_pr("7", True, now=self.NOW), "opened")
        self.assertEqual(len(self.posted), 1)
        self.assertEqual(self.edited, [])

    def test_a_parked_pr_gets_no_comment(self):
        self.history()
        self.assertEqual(conflicts.reconcile_pr("7", True, now=self.NOW, parked=True), "parked")
        self.assertEqual(self.posted, [])

    def test_a_parked_pr_still_closes_out_an_open_episode(self):
        # Otherwise the recorded duration would run forever and poison the median.
        onset = self.NOW - 5000
        self.history(self.open_episode(11, onset))
        self.assertEqual(conflicts.reconcile_pr("7", False, now=self.NOW, parked=True), "resolved")
        self.assertEqual(len(self.edited), 1)

    def test_dry_run_decides_but_writes_nothing(self):
        self.history()
        self.assertEqual(conflicts.reconcile_pr("7", True, now=self.NOW, dry_run=True), "opened")
        self.assertEqual((self.posted, self.edited), ([], []))


class Unknowns(unittest.TestCase):
    """UNKNOWN mergeability must never be read as either answer."""

    def setUp(self):
        self._open = conflicts.open_prs

    def tearDown(self):
        conflicts.open_prs = self._open

    def test_a_later_round_fills_in_what_the_first_could_not(self):
        rows = [{"number": 1, "conflicting": None}, {"number": 2, "conflicting": False}]
        conflicts.open_prs = lambda: [{"number": 1, "conflicting": True},
                                      {"number": 2, "conflicting": False}]
        conflicts.resolve_unknowns(rows, sleep=lambda s: None)
        self.assertEqual([r["conflicting"] for r in rows], [True, False])

    def test_a_permanently_unknown_pr_stays_unknown(self):
        rows = [{"number": 1, "conflicting": None}]
        calls = []
        def never_knows():
            calls.append(1)
            return [{"number": 1, "conflicting": None}]
        conflicts.open_prs = never_knows
        conflicts.resolve_unknowns(rows, sleep=lambda s: None)
        self.assertIsNone(rows[0]["conflicting"])
        self.assertEqual(len(calls), conflicts.UNKNOWN_ROUNDS - 1)

    def test_no_unknowns_costs_no_extra_request(self):
        rows = [{"number": 1, "conflicting": False}]
        conflicts.open_prs = lambda: self.fail("must not re-read when nothing is unknown")
        conflicts.resolve_unknowns(rows, sleep=lambda s: None)


class Sweep(unittest.TestCase):
    def setUp(self):
        self._open = conflicts.open_prs
        self._reconcile = conflicts.reconcile_pr
        self._render = conflicts._render
        self._sink = conflicts._zulip_sink
        self.reconciled, self.rendered = [], []
        conflicts._zulip_sink = lambda: None
        conflicts._render = lambda pr, c, sink, dry: self.rendered.append(pr) or 0

    def tearDown(self):
        conflicts.open_prs = self._open
        conflicts.reconcile_pr = self._reconcile
        conflicts._render = self._render
        conflicts._zulip_sink = self._sink

    def pr(self, number, conflicting, labels=None):
        return {"number": number, "title": "t", "draft": False,
                "conflicting": conflicting, "author": "alice", "labels": labels or []}

    def stub_prs(self, *prs):
        conflicts.open_prs = lambda: list(prs)

    def stub_actions(self, actions):
        def fake(pr, conflicting, now=None, dry_run=False, parked=False):
            self.reconciled.append((pr, conflicting, parked))
            return actions[pr]
        conflicts.reconcile_pr = fake

    def test_unknown_prs_are_skipped_entirely(self):
        self.stub_prs(self.pr(1, None), self.pr(2, False))
        self.stub_actions({2: "clear"})
        self.assertEqual(conflicts.sweep(use_zulip=False, sleep=lambda s: None), 0)
        self.assertEqual([row[0] for row in self.reconciled], [2])

    def test_a_hold_label_marks_the_pr_parked(self):
        self.stub_prs(self.pr(1, True, labels=["keep", "roadmap/PDE"]))
        self.stub_actions({1: "parked"})
        conflicts.sweep(use_zulip=False, sleep=lambda s: None)
        self.assertEqual(self.reconciled, [(1, True, True)])

    def test_a_changed_pr_is_re_rendered(self):
        self.stub_prs(self.pr(1, True))
        self.stub_actions({1: "opened"})
        conflicts.sweep(use_zulip=False, sleep=lambda s: None)
        self.assertEqual(self.rendered, [1])

    def test_an_unchanged_correctly_labelled_pr_is_left_alone(self):
        self.stub_prs(self.pr(1, True, labels=["merge-conflict"]),
                      self.pr(2, False, labels=["ready-to-merge"]))
        self.stub_actions({1: "ongoing", 2: "clear"})
        conflicts.sweep(use_zulip=False, sleep=lambda s: None)
        self.assertEqual(self.rendered, [])

    def test_a_stale_label_is_corrected_even_without_a_comment_change(self):
        # A PR that conflicts but was never labelled (the label write failed last
        # run) must still get its label, even though its comment is "ongoing".
        self.stub_prs(self.pr(1, True), self.pr(2, False, labels=["merge-conflict"]))
        self.stub_actions({1: "ongoing", 2: "clear"})
        conflicts.sweep(use_zulip=False, sleep=lambda s: None)
        self.assertEqual(self.rendered, [1, 2])

    def test_a_failing_pr_does_not_stop_the_others(self):
        def fake(pr, conflicting, now=None, dry_run=False, parked=False):
            if pr == 1:
                raise RuntimeError("GitHub said no")
            self.reconciled.append(pr)
            return "clear"
        self.stub_prs(self.pr(1, True), self.pr(2, False))
        conflicts.reconcile_pr = fake
        self.assertEqual(conflicts.sweep(use_zulip=False, sleep=lambda s: None), 1)
        self.assertEqual(self.reconciled, [2])


class Report(unittest.TestCase):
    NOW = 1_700_100_000

    def setUp(self):
        self._open = conflicts.open_prs
        self._comments = conflicts.conflict_comments

    def tearDown(self):
        conflicts.open_prs = self._open
        conflicts.conflict_comments = self._comments

    def stub(self, prs, comments):
        conflicts.open_prs = lambda: prs
        conflicts.conflict_comments = lambda pr: comments.get(pr, [])

    def episode(self, onset, resolved=None):
        marker = {"onset": onset}
        if resolved is not None:
            marker["resolved"] = resolved
        return {"id": 1, "marker": marker, "resolved": resolved is not None}

    def test_a_live_episode_is_measured_to_now(self):
        self.stub([{"number": 5, "author": "alice"}],
                  {5: [self.episode(self.NOW - 3600)]})
        [row] = conflicts.episodes(now=self.NOW)
        self.assertTrue(row["live"])
        self.assertEqual(row["seconds"], 3600)
        self.assertIsNone(row["resolved"])

    def test_a_resolved_episode_uses_its_recorded_span(self):
        self.stub([{"number": 5, "author": "alice"}],
                  {5: [self.episode(1000, 4600)]})
        [row] = conflicts.episodes(now=self.NOW)
        self.assertFalse(row["live"])
        self.assertEqual(row["seconds"], 3600)

    def test_days_filters_on_onset(self):
        self.stub([{"number": 5, "author": "alice"}],
                  {5: [self.episode(self.NOW - 10 * 86400), self.episode(self.NOW - 3600)]})
        self.assertEqual(len(conflicts.episodes(days=2, now=self.NOW)), 1)
        self.assertEqual(len(conflicts.episodes(now=self.NOW)), 2)

    def test_summary_reports_both_populations(self):
        self.stub([{"number": 5, "author": "alice"}, {"number": 6, "author": "bob"}],
                  {5: [self.episode(1000, 1000 + 7200)],
                   6: [self.episode(self.NOW - 86400)]})
        lines = "\n".join(conflicts.summarise(conflicts.episodes(now=self.NOW)))
        self.assertIn("2 conflict episode(s): 1 resolved, 1 live", lines)
        self.assertIn("LIVE #6", lines)
        self.assertIn("alice", lines)


class Formatting(unittest.TestCase):
    def test_durations_read_at_the_right_scale(self):
        self.assertEqual(conflicts.human_duration(59), "0m")
        self.assertEqual(conflicts.human_duration(3 * 3600 + 720), "3h 12m")
        self.assertEqual(conflicts.human_duration(2 * 86400 + 4 * 3600), "2d 4h")

    def test_median_of_an_even_count_averages_the_middle(self):
        self.assertEqual(conflicts.median([1, 2, 3, 4]), 2.5)
        self.assertEqual(conflicts.median([3, 1, 2]), 2)
        self.assertIsNone(conflicts.median([]))


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
        episodes, rewritten = self.analyse(mirror, self.pr())
        self.assertEqual(episodes, [])
        self.assertFalse(rewritten)

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
        _, rewritten = self.analyse(mirror, self.pr())
        self.assertTrue(rewritten)

    def test_a_pr_with_no_fetchable_head_is_skipped_not_guessed(self):
        mirror = self.FakeMirror([], {})
        self.assertEqual(self.analyse(mirror, self.pr()), ([], False))


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
        lines = "\n".join(conflict_stats.summarise(self.episodes(), rewritten=4, total_prs=99))
        self.assertIn("3 conflict episode(s) across 3 of 99 PR(s)", lines)
        self.assertIn("4 PR(s) had their history rewritten", lines)
        self.assertIn("1/2 took over 24h", lines)
        self.assertIn("1 while the author was already working the PR, 1 on a later return", lines)
        self.assertIn("still conflicting", lines)


if __name__ == "__main__":
    unittest.main()
