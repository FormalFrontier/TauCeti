#!/usr/bin/env python3
"""Unit tests for the merge-conflict sink: detection, the comment state machine, the report.

Pure logic only: GitHub reads/writes and `git` are stubbed, so these run with no
network, no `gh`, and no repository. Run with:  python3 test_conflicts.py
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
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
        self._saved = core.pr_comments

    def tearDown(self):
        core.pr_comments = self._saved

    def stub(self, *comments):
        core.pr_comments = lambda pr: list(comments)

    def comment(self, cid, onset, resolved=None, association="CONTRIBUTOR", is_bot=True):
        body = (conflicts.resolved_body(onset, resolved) if resolved
                else conflicts.conflict_body(onset))
        return {"id": cid, "body": body, "updated": "2026-01-01T00:00:00Z",
                "association": association, "is_bot": is_bot}

    def test_finds_its_own_app_authored_comment(self):
        # The regression that would have made every sweep post another comment: a
        # GitHub App installation bot is CONTRIBUTOR, which core.trusted_comments
        # excludes. Reading markers through that filter saw nothing, forever.
        self.stub(self.comment(10, 100, association="CONTRIBUTOR", is_bot=True))
        self.assertEqual(len(conflicts.conflict_comments("1")), 1)

    def test_finds_a_repo_associated_humans_comment(self):
        self.stub(self.comment(10, 100, association="MEMBER", is_bot=False))
        self.assertEqual(len(conflicts.conflict_comments("1")), 1)

    def test_ignores_a_marker_forged_by_an_outside_contributor(self):
        self.stub(self.comment(10, 100, association="CONTRIBUTOR", is_bot=False))
        self.assertEqual(conflicts.conflict_comments("1"), [])

    def test_ignores_a_marker_from_a_drive_by_account(self):
        self.stub(self.comment(10, 100, association="NONE", is_bot=False))
        self.assertEqual(conflicts.conflict_comments("1"), [])

    def test_orders_episodes_oldest_first(self):
        self.stub(self.comment(20, 300), self.comment(10, 100, 200))
        found = conflicts.conflict_comments("1")
        self.assertEqual([c["marker"]["onset"] for c in found], [100, 300])
        self.assertEqual([c["resolved"] for c in found], [True, False])

    def test_ignores_unrelated_comments(self):
        self.stub({"id": 1, "body": "<!--tauceti-scoreboard--> nope", "updated": "x",
                   "association": "MEMBER", "is_bot": False})
        self.assertEqual(conflicts.conflict_comments("1"), [])


class ReconcilePR(unittest.TestCase):
    """The comment state machine: opened / ongoing / resolved / clear / parked."""

    NOW = 1_700_100_000

    def setUp(self):
        self._comments = core.pr_comments
        self._post = conflicts.post_comment
        self._edit = conflicts.edit_comment
        self._still = conflicts.still_true
        self._onset = conflicts.label_onset
        self.posted, self.edited = [], []
        conflicts.post_comment = lambda pr, body: self.posted.append((pr, body))
        conflicts.edit_comment = lambda cid, body: self.edited.append((cid, body))
        conflicts.still_true = lambda pr, head, base, c: True
        conflicts.label_onset = lambda pr: None

    def tearDown(self):
        core.pr_comments = self._comments
        conflicts.post_comment = self._post
        conflicts.edit_comment = self._edit
        conflicts.still_true = self._still
        conflicts.label_onset = self._onset

    def history(self, *comments):
        core.pr_comments = lambda pr: list(comments)

    def open_episode(self, cid, onset):
        return {"id": cid, "body": conflicts.conflict_body(onset), "updated": "u",
                "association": "CONTRIBUTOR", "is_bot": True}

    def closed_episode(self, cid, onset, resolved):
        return {"id": cid, "body": conflicts.resolved_body(onset, resolved), "updated": "u",
                "association": "CONTRIBUTOR", "is_bot": True}

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

    def test_a_pr_that_moved_since_the_sweep_read_it_is_not_commented(self):
        # The author pushed between the queue read and this write; commenting now
        # would announce a conflict on a head that may already be fixed.
        self.history()
        conflicts.still_true = lambda pr, head, base, c: False
        self.assertEqual(
            conflicts.reconcile_pr("7", True, now=self.NOW, head="H", base="B"), "stale")
        self.assertEqual(self.posted, [])

    def test_a_pr_that_moved_does_not_get_its_episode_closed_out(self):
        # Resolving on a stale read would lose this episode's real onset.
        self.history(self.open_episode(11, self.NOW - 5000))
        conflicts.still_true = lambda pr, head, base, c: False
        self.assertEqual(
            conflicts.reconcile_pr("7", False, now=self.NOW, head="H", base="B"), "stale")
        self.assertEqual(self.edited, [])

    def test_the_confirmation_is_given_the_observed_head_and_base(self):
        seen = []
        self.history()
        conflicts.still_true = lambda pr, head, base, c: seen.append((pr, head, base, c)) or True
        conflicts.reconcile_pr("7", True, now=self.NOW, head="H1", base="B1")
        self.assertEqual(seen, [("7", "H1", "B1", True)])

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

    def test_an_unparked_conflict_is_dated_from_when_the_label_went_on(self):
        # The sweep saw this conflict two days ago, while the PR was parked: it
        # labelled it but wrote no comment. Dating the episode from now would report
        # a two-day-old conflict as brand new and quietly shorten the median.
        self.history()
        conflicts.label_onset = lambda pr: self.NOW - 2 * 86400
        self.assertEqual(
            conflicts.reconcile_pr("7", True, now=self.NOW, conflict_labelled=True),
            "opened")
        self.assertEqual(conflicts.parse_marker(self.posted[0][1]),
                         {"onset": self.NOW - 2 * 86400})

    def test_an_unreadable_label_history_still_posts_the_notice(self):
        # The onset degrades to "now"; the notice itself never depends on the label.
        self.history()
        conflicts.label_onset = lambda pr: None
        self.assertEqual(
            conflicts.reconcile_pr("7", True, now=self.NOW, conflict_labelled=True),
            "opened")
        self.assertEqual(conflicts.parse_marker(self.posted[0][1]), {"onset": self.NOW})

    def test_an_episode_is_never_dated_into_the_future(self):
        self.history()
        conflicts.label_onset = lambda pr: self.NOW + 500
        conflicts.reconcile_pr("7", True, now=self.NOW, conflict_labelled=True)
        self.assertEqual(conflicts.parse_marker(self.posted[0][1]), {"onset": self.NOW})

    def test_an_unlabelled_pr_costs_no_label_history_read(self):
        self.history()
        conflicts.label_onset = lambda pr: self.fail("must not read the label history")
        conflicts.reconcile_pr("7", True, now=self.NOW)
        self.assertEqual(conflicts.parse_marker(self.posted[0][1]), {"onset": self.NOW})

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

    def row(self, number, conflicting, head="H", base="B"):
        return {"number": number, "conflicting": conflicting, "head": head, "base": base}

    def test_a_later_round_fills_in_what_the_first_could_not(self):
        rows = [self.row(1, None), self.row(2, False)]
        conflicts.open_prs = lambda: [self.row(1, True), self.row(2, False)]
        conflicts.resolve_unknowns(rows, sleep=lambda s: None)
        self.assertEqual([r["conflicting"] for r in rows], [True, False])

    def test_an_answer_for_a_different_head_is_not_filled_in(self):
        # The author pushed between rounds: GitHub's answer is about the NEW head
        # and says nothing about the one we recorded.
        rows = [self.row(1, None, head="H1")]
        conflicts.open_prs = lambda: [self.row(1, True, head="H2")]
        conflicts.resolve_unknowns(rows, sleep=lambda s: None)
        self.assertIsNone(rows[0]["conflicting"])

    def test_a_permanently_unknown_pr_stays_unknown(self):
        rows = [self.row(1, None)]
        calls = []
        def never_knows():
            calls.append(1)
            return [self.row(1, None)]
        conflicts.open_prs = never_knows
        conflicts.resolve_unknowns(rows, sleep=lambda s: None)
        self.assertIsNone(rows[0]["conflicting"])
        self.assertEqual(len(calls), conflicts.UNKNOWN_ROUNDS - 1)

    def test_no_unknowns_costs_no_extra_request(self):
        rows = [self.row(1, False)]
        conflicts.open_prs = lambda: self.fail("must not re-read when nothing is unknown")
        conflicts.resolve_unknowns(rows, sleep=lambda s: None)


class StillTrue(unittest.TestCase):
    """The gate that stands between a stale observation and an irreversible write."""

    def setUp(self):
        self._api = core.gh_api

    def tearDown(self):
        core.gh_api = self._api

    def answer(self, payload):
        core.gh_api = lambda path, jq=None, paginate=False: payload

    def test_confirms_an_unchanged_conflicting_pr(self):
        self.answer('{"head":"H","base":"B","mergeable":false}')
        self.assertTrue(conflicts.still_true("1", "H", "B", True))

    def test_confirms_an_unchanged_mergeable_pr(self):
        self.answer('{"head":"H","base":"B","mergeable":true}')
        self.assertTrue(conflicts.still_true("1", "H", "B", False))

    def test_rejects_a_moved_head(self):
        self.answer('{"head":"H2","base":"B","mergeable":false}')
        self.assertFalse(conflicts.still_true("1", "H", "B", True))

    def test_rejects_a_moved_base(self):
        self.answer('{"head":"H","base":"B2","mergeable":false}')
        self.assertFalse(conflicts.still_true("1", "H", "B", True))

    def test_rejects_a_changed_verdict(self):
        self.answer('{"head":"H","base":"B","mergeable":true}')
        self.assertFalse(conflicts.still_true("1", "H", "B", True))

    def test_rejects_a_verdict_that_went_back_to_uncomputed(self):
        self.answer('{"head":"H","base":"B","mergeable":null}')
        self.assertFalse(conflicts.still_true("1", "H", "B", True))

    def test_a_failed_read_never_authorises_the_write(self):
        def boom(path, jq=None, paginate=False):
            raise RuntimeError("GitHub is down")
        core.gh_api = boom
        self.assertFalse(conflicts.still_true("1", "H", "B", True))


class LabelHistory(unittest.TestCase):
    """The label timeline: the record of an episode that was seen but never commented on."""

    def setUp(self):
        self._api = core.gh_api

    def tearDown(self):
        core.gh_api = self._api

    def answer(self, payload):
        core.gh_api = lambda path, jq=None, paginate=False: payload

    def test_reads_both_ends_of_an_episode_oldest_first(self):
        self.answer("2026-03-01T12:00:00Z labeled\n2026-01-01T00:00:00Z unlabeled\n")
        self.assertEqual(
            conflicts.label_events("7"),
            [(conflicts.iso_to_epoch("2026-01-01T00:00:00Z"), False),
             (conflicts.iso_to_epoch("2026-03-01T12:00:00Z"), True)])

    def test_a_failed_read_is_not_an_empty_history(self):
        # "We could not look" must not read as "it never happened": the caller falls
        # back to now for an onset, and reports no unannounced episode at all.
        def boom(path, jq=None, paginate=False):
            raise RuntimeError("GitHub is down")
        core.gh_api = boom
        self.assertIsNone(conflicts.label_events("7"))
        self.assertEqual(conflicts.unannounced_episodes("7", [], now=1_700_000_000), [])

    def test_takes_the_most_recent_application(self):
        # An earlier episode's label event is still in the history; only the current
        # application dates this one.
        self.answer("2026-01-01T00:00:00Z labeled\n2026-03-01T12:00:00Z labeled\n")
        self.assertEqual(conflicts.label_onset("7"),
                         conflicts.iso_to_epoch("2026-03-01T12:00:00Z"))

    def test_no_recorded_application_reads_as_unknown(self):
        self.answer("")
        self.assertIsNone(conflicts.label_onset("7"))

    def test_a_failed_read_reads_as_unknown(self):
        def boom(path, jq=None, paginate=False):
            raise RuntimeError("GitHub is down")
        core.gh_api = boom
        self.assertIsNone(conflicts.label_onset("7"))


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
        return {"number": number, "title": "t", "draft": False, "head": "H", "base": "B",
                "conflicting": conflicting, "author": "alice", "labels": labels or []}

    def stub_prs(self, *prs):
        conflicts.open_prs = lambda: list(prs)

    def stub_actions(self, actions):
        def fake(pr, conflicting, now=None, dry_run=False, parked=False, head=None,
                 base=None, conflict_labelled=False):
            self.reconciled.append((pr, conflicting, parked, conflict_labelled))
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
        self.assertEqual(self.reconciled, [(1, True, True, False)])

    def test_an_already_labelled_pr_is_reconciled_as_such(self):
        # How a conflict first seen while the PR was parked keeps its real onset.
        self.stub_prs(self.pr(1, True, labels=["merge-conflict"]))
        self.stub_actions({1: "opened"})
        conflicts.sweep(use_zulip=False, sleep=lambda s: None)
        self.assertEqual(self.reconciled, [(1, True, False, True)])

    def test_a_changed_pr_is_re_rendered(self):
        self.stub_prs(self.pr(1, True))
        self.stub_actions({1: "opened"})
        conflicts.sweep(use_zulip=False, sleep=lambda s: None)
        self.assertEqual(self.rendered, [1])

    def test_a_live_conflict_is_re_rendered_every_sweep(self):
        # Nothing else fires for a conflicting PR -- that is this module's premise --
        # so a label or a ⚠️ lost to a failed write is only ever restored here. An
        # unchanged, correctly-labelled conflict is still re-asserted; both sinks are
        # convergent, so agreeing costs reads and no writes.
        self.stub_prs(self.pr(1, True, labels=["merge-conflict"]))
        self.stub_actions({1: "ongoing"})
        conflicts.sweep(use_zulip=False, sleep=lambda s: None)
        self.assertEqual(self.rendered, [1])

    def test_an_unchanged_mergeable_pr_is_left_alone(self):
        # Off an episode the PR's own events reconcile it, so the sweep pays nothing.
        self.stub_prs(self.pr(2, False, labels=["ready-to-merge"]))
        self.stub_actions({2: "clear"})
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
        def fake(pr, conflicting, now=None, dry_run=False, parked=False, head=None,
                 base=None, conflict_labelled=False):
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
        self._comments = conflicts.conflict_comments
        self._events = conflicts.label_events
        self.prs = []
        conflicts.label_events = lambda pr: []

    def tearDown(self):
        conflicts.conflict_comments = self._comments
        conflicts.label_events = self._events

    def run_episodes(self, **kwargs):
        return conflicts.episodes(now=self.NOW, prs=self.prs, **kwargs)

    def stub(self, prs, comments, events=None):
        self.prs = prs
        conflicts.conflict_comments = lambda pr: comments.get(pr, [])
        conflicts.label_events = lambda pr: (events or {}).get(pr, [])

    def episode(self, onset, resolved=None):
        marker = {"onset": onset}
        if resolved is not None:
            marker["resolved"] = resolved
        return {"id": 1, "marker": marker, "resolved": resolved is not None}

    def test_a_live_episode_is_measured_to_now(self):
        self.stub([{"number": 5, "author": "alice"}],
                  {5: [self.episode(self.NOW - 3600)]})
        [row] = self.run_episodes()
        self.assertEqual(row["state"], "live")
        self.assertEqual(row["seconds"], 3600)
        self.assertIsNone(row["resolved"])

    def test_a_resolved_episode_uses_its_recorded_span(self):
        self.stub([{"number": 5, "author": "alice"}],
                  {5: [self.episode(self.NOW - 3600, self.NOW)]})
        [row] = self.run_episodes()
        self.assertEqual(row["state"], "resolved")
        self.assertEqual(row["seconds"], 3600)

    def test_days_filters_on_onset(self):
        self.stub([{"number": 5, "author": "alice"}],
                  {5: [self.episode(self.NOW - 10 * 86400), self.episode(self.NOW - 3600)]})
        self.assertEqual(len(self.run_episodes(days=2)), 1)
        self.assertEqual(len(self.run_episodes(days=90)), 2)

    def test_the_reported_median_averages_an_even_count(self):
        self.stub([{"number": 5, "author": "alice"}], {5: [
            self.episode(self.NOW - 90000, self.NOW - 86400),   # 1h
            self.episode(self.NOW - 80000, self.NOW - 69200),   # 3h
        ]})
        lines = "\n".join(conflicts.summarise(self.run_episodes(days=90)))
        self.assertIn("resolved: median 2h 0m", lines)

    def test_summary_reports_both_populations(self):
        self.stub([{"number": 5, "author": "alice"}, {"number": 6, "author": "bob"}],
                  {5: [self.episode(self.NOW - 90000, self.NOW - 82800)],
                   6: [self.episode(self.NOW - 86400)]})
        lines = "\n".join(conflicts.summarise(self.run_episodes(days=90)))
        self.assertIn("2 conflict episode(s): 1 resolved, 1 live", lines)
        self.assertIn("LIVE #6", lines)
        self.assertIn("alice", lines)

    def test_a_conflict_that_came_and_went_while_parked_is_still_measured(self):
        # The episode nobody was told about: a parked PR gets the label and no
        # comment, so the marker history is empty and only the label brackets it.
        # Dropping it would drop precisely the conflicts nobody was chasing.
        self.stub([{"number": 5, "author": "alice"}], {},
                  {5: [(self.NOW - 4 * 86400, True), (self.NOW - 86400, False)]})
        [row] = self.run_episodes(days=90)
        self.assertEqual((row["state"], row["announced"]), ("resolved", False))
        self.assertEqual(row["seconds"], 3 * 86400)
        self.assertEqual(row["resolved"], self.NOW - 86400)

    def test_a_still_parked_conflict_is_live_not_resolved(self):
        self.stub([{"number": 5, "author": "alice"}], {},
                  {5: [(self.NOW - 7200, True)]})
        [row] = self.run_episodes(days=90)
        self.assertEqual((row["state"], row["seconds"], row["announced"]),
                         ("live", 7200, False))

    def test_a_pr_closed_while_still_labelled_is_censored(self):
        self.stub([{"number": 5, "author": "alice",
                    "closed_at": "2026-01-01T00:00:00Z"}], {},
                  {5: [(conflicts.iso_to_epoch("2025-12-31T00:00:00Z"), True)]})
        [row] = self.run_episodes(days=90000)
        self.assertEqual((row["state"], row["seconds"]), ("censored", 86400))

    def test_an_announced_episode_is_not_counted_twice_by_its_own_label(self):
        # Every episode moves the label too, so the label span that brackets a
        # commented episode is that same episode -- counted once, from the marker.
        onset = self.NOW - 5000
        self.stub([{"number": 5, "author": "alice"}],
                  {5: [self.episode(onset, self.NOW - 1000)]},
                  {5: [(onset - 30, True), (self.NOW - 1000, False)]})
        [row] = self.run_episodes(days=90)
        self.assertEqual((row["onset"], row["announced"]), (onset, True))

    def test_the_parked_population_is_reported_separately(self):
        self.stub([{"number": 5, "author": "alice"}, {"number": 6, "author": "bob"}],
                  {5: [self.episode(self.NOW - 90000, self.NOW - 86400)]},        # 1h
                  {6: [(self.NOW - 90000, True), (self.NOW - 79200, False)]})     # 3h
        lines = "\n".join(conflicts.summarise(self.run_episodes(days=90)))
        # Queue-wide first (the number the 24h target names), then the split.
        self.assertIn("resolved: median 2h 0m", lines)
        self.assertIn("parked:   1 episode(s) were never announced", lines)
        self.assertIn("no comment was posted), median 3h 0m", lines)
        self.assertIn("announced episodes alone resolve in a median of 1h 0m", lines)


class Writes(unittest.TestCase):
    """Both comment writes go through core's runner, and so inherit its back-off."""

    def setUp(self):
        self._api = core.gh_api
        self.calls = []
        core.gh_api = lambda path, jq=None, paginate=False, method=None, fields=None: (
            self.calls.append((path, method, fields)))

    def tearDown(self):
        core.gh_api = self._api

    def test_a_notice_is_posted_through_the_shared_runner(self):
        conflicts.post_comment("7", "hello")
        self.assertEqual(
            self.calls,
            [(f"/repos/{conflicts.REPO}/issues/7/comments", "POST", {"body": "hello"})])

    def test_a_resolution_is_edited_through_the_shared_runner(self):
        conflicts.edit_comment(11, "done")
        self.assertEqual(
            self.calls,
            [(f"/repos/{conflicts.REPO}/issues/comments/11", "PATCH", {"body": "done"})])


class Formatting(unittest.TestCase):
    def test_durations_read_at_the_right_scale(self):
        self.assertEqual(conflicts.human_duration(59), "0m")
        self.assertEqual(conflicts.human_duration(3 * 3600 + 720), "3h 12m")
        self.assertEqual(conflicts.human_duration(2 * 86400 + 4 * 3600), "2d 4h")


if __name__ == "__main__":
    unittest.main()
