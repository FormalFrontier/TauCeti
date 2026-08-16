#!/usr/bin/env python3
"""Unit tests for the invariants that make stuck_alerts a trustworthy watchdog.

Focus on the failure modes that would make it silently wrong rather than merely
noisy: fail-open resolution, multi-page JSON parsing, marker-injection safety, and
recurrence visibility. Pure logic only -- GitHub and Zulip are faked, so no network
or `gh` is needed. Run: python3 scripts/pr_status/test_stuck_alerts.py
"""

import os
import unittest

os.environ.setdefault("ZULIP_CHANNEL", "Tau Ceti")
os.environ.setdefault("ZULIP_TOPIC", "Stuck PRs")

import stuck_alerts as sa  # noqa: E402
import core  # noqa: E402
import zulip as zp  # noqa: E402


class FakeZulip:
    """Records send/update calls; returns a scripted message list from the topic."""

    def __init__(self, messages, bot_id=7):
        self._messages = messages
        self._bot_id = bot_id
        self.sent = []
        self.updated = []

    def my_user_id(self):
        return self._bot_id

    def get_messages(self, narrow):
        return self._messages

    def send_message(self, content):
        self.sent.append(content)
        return len(self.sent)

    def update_message(self, mid, content):
        self.updated.append((mid, content))


def msg(mid, content, sender=7):
    return {"id": mid, "content": content, "sender_id": sender}


def active_content(key, title="T", body="B"):
    return sa.alert_content({"key": key, "title": title, "body": body})


class GhStreamTest(unittest.TestCase):
    def test_parses_jsonl_across_pages(self):
        # `gh --paginate --jq '.[] | {..}'` concatenates per-page streams: three
        # objects over two "pages". A single json.loads would choke on line 2+.
        pages = '{"number": 1}\n{"number": 2}\n{"number": 3}\n'
        self.addCleanup(setattr, zp, "gh_api", core.gh_api)
        core.gh_api = lambda path, jq=None, paginate=False: pages
        got = sa.gh_stream("/x", jq=".[] | {number}")
        self.assertEqual([r["number"] for r in got], [1, 2, 3])

    def test_empty_output_is_empty_list(self):
        self.addCleanup(setattr, zp, "gh_api", core.gh_api)
        core.gh_api = lambda path, jq=None, paginate=False: "\n"
        self.assertEqual(sa.gh_stream("/x", jq=".[]"), [])

    def test_gh_lines_returns_raw_strings_not_json(self):
        # `.[].filename` emits bare filenames; gh_lines must NOT json.loads them
        # (json.loads("TauCeti/Foo.lean") would raise) -- the bug that broke
        # stranded-pr when it used gh_stream here.
        self.addCleanup(setattr, zp, "gh_api", core.gh_api)
        core.gh_api = lambda path, jq=None, paginate=False: "TauCeti/Foo.lean\nlean-toolchain\n"
        self.assertEqual(sa.gh_lines("/x", jq=".[].filename"),
                         ["TauCeti/Foo.lean", "lean-toolchain"])


class MainRedTest(unittest.TestCase):
    """A moving main tip must not hide the last conclusive red CI run."""

    @staticmethod
    def _run(head, status="completed", conclusion="success"):
        return {"head_sha": head, "status": status, "conclusion": conclusion}

    def _install_runs(self, runs, tip="tip"):
        import json
        payload = "".join(json.dumps(run) + "\n" for run in runs)
        return _install(self, [("/commits/main", tip), ("ci.yml/runs", payload)])

    def test_tip_failure_alerts(self):
        fake = self._install_runs([self._run("tip", conclusion="failure")])
        self.assertEqual([a["key"] for a in sa.detect_main_red()], ["main-red"])
        runs_request = next(path for path, _jq, _paginate in fake.requests
                            if "ci.yml/runs" in path)
        self.assertIn("branch=main", runs_request)
        self.assertIn("event=push", runs_request)
        self.assertIn("per_page=100", runs_request)
        self.assertFalse(next(paginate for path, _jq, paginate in fake.requests
                              if "ci.yml/runs" in path))

    def test_moving_tip_does_not_hide_previous_failure(self):
        # Regression: the old detector returned early because `tip` was still
        # running, even though every completed main run behind it was red.
        self._install_runs([
            self._run("tip", status="in_progress", conclusion=""),
            self._run("bad", conclusion="failure"),
        ])
        alert = sa.detect_main_red()[0]
        self.assertIn("`bad`", alert["body"])
        self.assertIn("current tip `tip`", alert["body"])

    def test_known_green_before_running_tip_is_not_an_alert(self):
        self._install_runs([
            self._run("tip", status="queued", conclusion=""),
            self._run("green"),
            self._run("old-bad", conclusion="failure"),
        ])
        self.assertEqual(sa.detect_main_red(), [])

    def test_cancellation_does_not_clear_known_red(self):
        self._install_runs([
            self._run("tip", conclusion="cancelled"),
            self._run("bad", conclusion="timed_out"),
        ])
        self.assertEqual([a["key"] for a in sa.detect_main_red()], ["main-red"])

    def test_new_success_clears_older_failure(self):
        self._install_runs([
            self._run("tip"),
            self._run("old-bad", conclusion="startup_failure"),
        ])
        self.assertEqual(sa.detect_main_red(), [])

    def test_no_conclusive_run_is_not_an_alert(self):
        self._install_runs([
            self._run("tip", status="in_progress", conclusion=""),
            self._run("old", conclusion="cancelled"),
        ])
        self.assertEqual(sa.detect_main_red(), [])

    def test_full_inconclusive_window_fails_closed(self):
        self._install_runs([
            self._run(f"run-{i}", conclusion="cancelled")
            for i in range(sa.MAIN_CI_WINDOW)
        ])
        with self.assertRaisesRegex(RuntimeError, "no conclusive main CI run"):
            sa.detect_main_red()


class FailClosedTest(unittest.TestCase):
    def test_failing_detector_records_prefix_and_keeps_others(self):
        self.addCleanup(setattr, sa, "DETECTORS", sa.DETECTORS)
        def boom():
            raise RuntimeError("api down")
        def ok():
            return [{"key": "main-red", "title": "t", "body": "b"}]
        sa.DETECTORS = [("stuck-bump", boom), ("main-red", ok)]
        alerts, failed = sa.collect_alerts()
        self.assertEqual([a["key"] for a in alerts], ["main-red"])
        self.assertEqual(failed, {"stuck-bump"})

    def test_reconcile_does_not_resolve_failed_prefix(self):
        # An existing stuck-bump alert is live; its detector failed this run, so it
        # must NOT be edited to resolved (that would turn a real emergency green).
        z = FakeZulip([msg(1, active_content("stuck-bump/1057"))])
        sa.reconcile(z, alerts=[], failed={"stuck-bump"}, dry_run=False)
        self.assertEqual(z.updated, [])
        self.assertEqual(z.sent, [])

    def test_reconcile_resolves_absent_alert_from_clean_detector(self):
        z = FakeZulip([msg(1, active_content("main-red"))])
        sa.reconcile(z, alerts=[], failed=set(), dry_run=False)
        self.assertEqual(len(z.updated), 1)
        self.assertTrue(z.updated[0][1].lstrip().startswith(sa.GREEN))


class AutoMergeScopeTest(unittest.TestCase):
    def test_lakefile_is_never_in_auto_merge_scope(self):
        files = ["lakefile.toml", "lake-manifest.json"]
        self.assertFalse(sa.is_automerge_scope(files))

    def test_other_infrastructure_is_not_in_auto_merge_scope(self):
        self.assertFalse(sa.is_automerge_scope(
            ["lakefile.toml", ".github/workflows/x.yml"]))


class ReconcileTest(unittest.TestCase):
    def test_new_alert_posts_message(self):
        z = FakeZulip([])
        sa.reconcile(z, [{"key": "main-red", "title": "t", "body": "b"}], set(), False)
        self.assertEqual(len(z.sent), 1)
        self.assertEqual(z.updated, [])

    def test_ongoing_alert_is_untouched(self):
        content = active_content("main-red", "t", "b")
        z = FakeZulip([msg(1, content)])
        sa.reconcile(z, [{"key": "main-red", "title": "t", "body": "b"}], set(), False)
        self.assertEqual(z.sent, [])
        self.assertEqual(z.updated, [])  # byte-identical -> no churn

    def test_recurrence_posts_new_message_not_edit(self):
        # Latest message for the key is already resolved (✅); a re-fire must post a
        # NEW message (edits do not notify watchers on a silent topic).
        resolved = sa.resolved_content("main-red", "main is RED")
        z = FakeZulip([msg(5, resolved)])
        sa.reconcile(z, [{"key": "main-red", "title": "t", "body": "b"}], set(), False)
        self.assertEqual(len(z.sent), 1)
        self.assertEqual(z.updated, [])


class ReviewStuckTest(unittest.TestCase):
    """An issue outliving its PR must not alert; anything unreadable still must."""

    ISSUES = '{"number": 1137, "title": "Review stuck: PR #1134"}\n'

    def fake_gh(self, pr_state):
        """Serve the issue list, then `pr_state` for the PR lookup (or raise)."""
        def gh_api(path, jq=None, paginate=False):
            if path.startswith("/repos/") and "/pulls/" in path:
                if isinstance(pr_state, Exception):
                    raise pr_state
                return pr_state + "\n"
            return self.ISSUES
        self.addCleanup(setattr, core, "gh_api", core.gh_api)
        core.gh_api = gh_api

    def test_open_pr_alerts(self):
        self.fake_gh("open")
        self.assertEqual([a["key"] for a in sa.detect_review_stuck()],
                         ["review-stuck/1137"])

    def test_finished_pr_does_not_alert(self):
        # The exact shape of issue #1137: its PR #1134 merged, the worker never
        # closed the issue, and the alert fired for two days.
        self.fake_gh("closed")
        self.assertEqual(sa.detect_review_stuck(), [])

    def test_unreadable_pr_state_still_alerts(self):
        # Fail closed: an API blip must never silence a live wedge.
        self.fake_gh(RuntimeError("gh api failed: 502"))
        self.assertEqual([a["key"] for a in sa.detect_review_stuck()],
                         ["review-stuck/1137"])

    def test_alert_body_names_only_the_issue(self):
        # The PR number reaches an API path and nothing else: no untrusted title
        # text, and no PR reference, may enter the rendered message.
        self.fake_gh("open")
        body = sa.detect_review_stuck()[0]["body"]
        self.assertIn("/issues/1137", body)
        self.assertNotIn("1134", body)


class MarkerSafetyTest(unittest.TestCase):
    def test_valid_trailing_marker_parses(self):
        self.assertEqual(sa.parse_marker(active_content("stale-fkb/917")), "stale-fkb/917")

    def test_marker_must_be_at_end(self):
        # A marker followed by more text is not our trailer -> not parsed as a key.
        body = "x <!--stuck:v1 stale-pin--> then more text"
        self.assertIsNone(sa.parse_marker(body))

    def test_injected_marker_does_not_hijack_key(self):
        # Simulate a message whose visible text embeds a marker but whose real
        # trailer is a different key. Only the trailing, grammar-valid key wins.
        content = ("🔴 **Review stuck <!--stuck:v1 stale-pin-->**\n\nbody\n\n"
                   "<!--stuck:v1 review-stuck/42-->")
        self.assertEqual(sa.parse_marker(content), "review-stuck/42")

    def test_bad_grammar_key_rejected(self):
        self.assertIsNone(sa.parse_marker("<!--stuck:v1 Has Spaces-->"))

    def test_newest_message_wins_per_key(self):
        old = msg(1, active_content("main-red"))
        new = msg(9, sa.resolved_content("main-red", "main is RED"))
        got = sa.newest_by_key([old, new], bot_id=7)
        self.assertEqual(got["main-red"]["id"], 9)

    def test_other_senders_ignored(self):
        mine = msg(1, active_content("main-red"), sender=7)
        theirs = msg(2, active_content("main-red"), sender=99)
        got = sa.newest_by_key([mine, theirs], bot_id=7)
        self.assertEqual(got["main-red"]["id"], 1)




# ----- blind spots the detectors used to have --------------------------------

def _ago(hours):
    """An ISO timestamp `hours` in the past, in the format the GitHub API returns."""
    import datetime as _dt
    t = sa.now_utc() - _dt.timedelta(hours=hours)
    return t.strftime("%Y-%m-%dT%H:%M:%SZ")


class RoutedGh:
    """Fakes core.gh_api by matching substrings of the request (path, then jq), in order.

    Two detectors read the same timeline path with different jq filters, so the jq is part
    of what identifies a request.
    """

    def __init__(self, routes):
        self.routes = routes
        self.requests = []

    def __call__(self, path, jq=None, paginate=False):
        self.requests.append((path, jq, paginate))
        request = f"{path} {jq or ''}"
        for needle, payload in self.routes:
            if needle in request:
                return payload
        return ""


def _install(test, routes):
    test.addCleanup(setattr, core, "gh_api", core.gh_api)
    fake = RoutedGh(routes)
    core.gh_api = fake
    return fake


class ReadyLabelClockTest(unittest.TestCase):
    """The strand clock must not reset when the merge queue churns a PR."""

    def _timeline(self, *events):
        return "".join(__import__("json").dumps(e) + "\n" for e in events)

    def test_reports_latest_application(self):
        _install(self, [("/timeline", self._timeline(
            {"event": "labeled", "at": "2026-08-01T00:00:00Z"},
            {"event": "unlabeled", "at": "2026-08-02T00:00:00Z"},
            {"event": "labeled", "at": "2026-08-03T00:00:00Z"}))])
        self.assertEqual(sa.ready_label_applied_at(1), "2026-08-03T00:00:00Z")

    def test_none_when_currently_removed(self):
        _install(self, [("/timeline", self._timeline(
            {"event": "labeled", "at": "2026-08-01T00:00:00Z"},
            {"event": "unlabeled", "at": "2026-08-02T00:00:00Z"}))])
        self.assertIsNone(sa.ready_label_applied_at(1))

    def test_queue_churn_does_not_reset_the_clock(self):
        # The regression this replaced: `updated_at` bumps on every enqueue/eviction, so a PR
        # bouncing every couple of hours could never reach STRANDED_HOURS. The label is old
        # even though the PR was "updated" minutes ago, so the strand must still be visible.
        _install(self, [("/timeline", self._timeline(
            {"event": "labeled", "at": _ago(30)}))])
        applied = sa.ready_label_applied_at(99)
        self.assertGreater(sa.hours_since(applied), sa.STRANDED_HOURS)


class EvictionLoopTest(unittest.TestCase):
    def _routes(self, removals, labels=("ready-to-merge",), ready_at=None):
        import json as _j
        prs = _j.dumps({"number": 7, "head": "abc", "draft": False,
                        "updated_at": _ago(1), "head_ref": "b", "head_repo": "o/r",
                        "author": "a", "labels": list(labels)}) + "\n"
        tl = "".join(_j.dumps({"at": t}) + "\n" for t in removals)
        label_events = _j.dumps({"event": "labeled", "at": ready_at or _ago(48)}) + "\n"
        return [("/pulls?state=open", prs),
                ("ready-to-merge", label_events),
                ("removed_from_merge_queue", tl)]

    def test_two_recent_evictions_alert(self):
        _install(self, self._routes([_ago(1), _ago(3)]))
        got = sa.detect_eviction_loops()
        self.assertEqual([a["key"] for a in got], ["eviction-loop/7"])

    def test_single_eviction_is_not_a_loop(self):
        _install(self, self._routes([_ago(1)]))
        self.assertEqual(sa.detect_eviction_loops(), [])

    def test_evictions_outside_the_window_do_not_count(self):
        _install(self, self._routes([_ago(30), _ago(40)]))
        self.assertEqual(sa.detect_eviction_loops(), [])

    def test_evictions_before_the_current_readiness_do_not_count(self):
        # The PR bounced twice, then the author pushed a fix and the label came back. Those
        # evictions belong to the previous cycle and say nothing about the current head.
        _install(self, self._routes([_ago(5), _ago(6)], ready_at=_ago(3)))
        self.assertEqual(sa.detect_eviction_loops(), [])

    def test_pr_not_marked_ready_is_skipped(self):
        _install(self, self._routes([_ago(1), _ago(2)], labels=("awaiting-author",)))
        self.assertEqual(sa.detect_eviction_loops(), [])


class MissingStatusTest(unittest.TestCase):
    def _routes(self, build_status, runs):
        import json as _j
        prs = _j.dumps({"number": 8, "head": "def", "draft": False,
                        "updated_at": _ago(1), "head_ref": "b", "head_repo": "o/r",
                        "author": "a", "labels": []}) + "\n"
        # The API returns runs newest first; so does this list.
        return [("/pulls?state=open", prs),
                ("/statuses", build_status),
                ("pr-build.yml/runs", "".join(_j.dumps(r) + "\n" for r in runs))]

    @staticmethod
    def _run(hours_ago, conclusion="failure", status="completed"):
        return {"status": status, "conclusion": conclusion, "updated_at": _ago(hours_ago)}

    def test_alerts_when_run_finished_but_no_status(self):
        _install(self, self._routes("", [self._run(2)]))
        self.assertEqual([a["key"] for a in sa.detect_missing_required_status()],
                         ["missing-status/8"])

    def test_silent_while_the_build_is_still_running(self):
        # No run at all yet: this is ordinary `awaiting-CI`, never an alert.
        _install(self, self._routes("", []))
        self.assertEqual(sa.detect_missing_required_status(), [])

    def test_silent_while_a_rerun_is_in_progress(self):
        # An earlier run concluded, but the head is building again right now; the status it
        # will post has simply not landed yet.
        _install(self, self._routes(
            "", [self._run(0.1, conclusion="", status="in_progress"), self._run(2)]))
        self.assertEqual(sa.detect_missing_required_status(), [])

    def test_cancelled_run_is_not_proof_of_a_missing_status(self):
        # A cancelled run (concurrency or manual) never reaches its reporting step, so it
        # posting no status is by design, not a wedge.
        _install(self, self._routes("", [self._run(2, conclusion="cancelled")]))
        self.assertEqual(sa.detect_missing_required_status(), [])

    def test_older_concluded_run_still_alerts_behind_a_cancellation(self):
        # The run that reported is the older one; a later cancellation does not excuse the
        # status it never posted.
        _install(self, self._routes(
            "", [self._run(0.6, conclusion="cancelled"), self._run(2, conclusion="success")]))
        self.assertEqual([a["key"] for a in sa.detect_missing_required_status()],
                         ["missing-status/8"])

    def test_silent_when_the_status_exists(self):
        _install(self, self._routes(
            '{"state": "failure", "updated_at": "2026-08-01T00:00:00Z"}', [self._run(2)]))
        self.assertEqual(sa.detect_missing_required_status(), [])


class DivergedHeadTest(unittest.TestCase):
    def _routes(self, tip):
        import json as _j
        prs = _j.dumps({"number": 9, "head": "aaaaaaaa", "draft": False,
                        "updated_at": _ago(1), "head_ref": "feat", "head_repo": "fork/TauCeti",
                        "author": "a", "labels": []}) + "\n"
        return [("/pulls?state=open", prs), ("/branches/", tip)]

    def test_alerts_when_head_is_behind_the_branch_tip(self):
        _install(self, self._routes("bbbbbbbb"))
        self.assertEqual([a["key"] for a in sa.detect_diverged_head()], ["diverged-head/9"])

    def test_silent_when_head_matches(self):
        _install(self, self._routes("aaaaaaaa"))
        self.assertEqual(sa.detect_diverged_head(), [])

    def test_silent_when_branch_is_unreadable(self):
        # A deleted head repo/branch is a different problem; do not cry wolf on an API miss.
        _install(self, self._routes(""))
        self.assertEqual(sa.detect_diverged_head(), [])

if __name__ == "__main__":
    unittest.main()
