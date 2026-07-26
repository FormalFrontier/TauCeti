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


if __name__ == "__main__":
    unittest.main()
