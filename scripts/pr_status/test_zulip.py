#!/usr/bin/env python3
"""Unit tests for Zulip PR post rendering and review reactions."""

import io
import json
import os
import sys
import unittest
from unittest import mock

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import labels  # noqa: E402
import zulip  # noqa: E402


class ReviewEmoji(unittest.TestCase):
    def emoji(self, review="none", inprogress=False):
        return zulip.review_emoji({
            "lifecycle": "open",
            "ci": "success",
            "review": review,
            "review_inprogress": inprogress,
            "head": "h",
            "title": "t",
        })

    def test_waiting_for_review_has_no_reaction(self):
        self.assertIsNone(self.emoji())
        self.assertIsNone(self.emoji(review="running"))

    def test_live_review_marker_is_eyes(self):
        self.assertEqual(self.emoji(inprogress=True), "eyes")
        self.assertEqual(self.emoji(review="running", inprogress=True), "eyes")

    def test_completed_blocking_review_is_writing(self):
        self.assertEqual(self.emoji(review="changes"), "writing")

    def test_completed_green_review_is_check(self):
        self.assertEqual(self.emoji(review="approved"), "check")

    def test_verdict_wins_over_leftover_marker(self):
        self.assertEqual(self.emoji(review="changes", inprogress=True), "writing")
        self.assertEqual(self.emoji(review="approved", inprogress=True), "check")

    def test_tracks_the_review_status_label_transitions(self):
        cases = [
            ("none", False, "awaiting-review", None),
            ("none", True, "review-in-progress", "eyes"),
            ("changes", False, "awaiting-author", "writing"),
            ("approved", False, "ready-to-merge", "check"),
        ]
        for review, inprogress, expected_label, expected_emoji in cases:
            status = {
                "lifecycle": "open",
                "ci": "success",
                "review": review,
                "review_inprogress": inprogress,
                "head": "h",
                "title": "t",
            }
            with self.subTest(review=review, inprogress=inprogress):
                self.assertEqual(labels.derived_label(status), expected_label)
                self.assertEqual(zulip.review_emoji(status), expected_emoji)


class MessageContent(unittest.TestCase):
    def test_includes_author_and_roadmap(self):
        content = zulip.pr_message_content(
            "1520",
            "feat: symmetric Rouché",
            "jeremy-kahn-brown-ai",
            ["roadmap/ConformalMapping"],
        )
        self.assertIn("https://github.com/TauCetiProject/TauCeti/pull/1520", content)
        self.assertIn(
            "[jeremy-kahn-brown-ai](https://github.com/jeremy-kahn-brown-ai)",
            content,
        )
        self.assertIn("roadmap: ConformalMapping", content)

    def test_multiple_or_missing_roadmaps(self):
        content = zulip.pr_message_content("1", "title", "author", ["roadmap/A", "roadmap/B"])
        self.assertIn("roadmap: A, B", content)
        missing = zulip.pr_message_content("1", "title", "author", [])
        self.assertIn("roadmap: unlabelled", missing)

    def test_bot_author_is_plain_text(self):
        content = zulip.pr_message_content(
            "1", "title", "tauceti-review-bot[bot]", ["roadmap/none"])
        self.assertIn("author: tauceti-review-bot[bot]", content)
        self.assertNotIn("github.com/tauceti-review-bot", content)
        self.assertIn("roadmap: none", content)

    def test_metadata_is_sanitized(self):
        content = zulip.pr_message_content("1", "@title #12", "@author", ["roadmap/#area"])
        self.assertNotIn("@title", content)
        self.assertNotIn("#12", content)
        self.assertNotIn("roadmap/#area", content)
        self.assertNotIn("[@author]", content)


class FindMessage(unittest.TestCase):
    class FakeZulip:
        def __init__(self, message):
            self.message = message
            self.searches = []

        def get_messages(self, narrow, num_before=1000):
            query = narrow[-1]["operand"]
            self.searches.append(query)
            return [self.message] if query in self.message["content"] else []

    def test_finds_pre_transfer_message(self):
        old_url = "https://github.com/FormalFrontier/TauCeti/pull/12"
        z = self.FakeZulip({"id": 7, "sender_id": 42, "content": old_url, "reactions": []})
        self.assertEqual(zulip.find_message(z, "12", 42)["id"], 7)
        self.assertEqual(len(z.searches), 2)

    def test_ignores_another_authors_matching_message(self):
        url = "https://github.com/TauCetiProject/TauCeti/pull/12"
        z = self.FakeZulip({"id": 7, "sender_id": 99, "content": url, "reactions": []})
        self.assertIsNone(zulip.find_message(z, "12", 42))


class StrictMode(unittest.TestCase):
    def run_main(self, *extra):
        with (
            mock.patch.dict(
                os.environ,
                {"ZULIP_EMAIL": "bot@example.com", "ZULIP_API_KEY": "secret"},
            ),
            mock.patch.object(zulip, "Zulip", return_value=object()),
            mock.patch.object(zulip, "reconcile", side_effect=RuntimeError("boom")),
        ):
            return zulip.main(["zulip.py", "reconcile", "12", *extra])

    def test_normal_reconcile_keeps_transient_failure_cosmetic(self):
        self.assertEqual(self.run_main(), 0)

    def test_strict_reconcile_fails_on_transient_failure(self):
        self.assertEqual(self.run_main("--strict"), 1)


class Reconcile(unittest.TestCase):
    class FakeZulip(FindMessage.FakeZulip):
        def __init__(self, message):
            super().__init__(message)
            self.updated = []
            self.sent = []
            self.added = []
            self.removed = []

        def get_messages(self, narrow, num_before=1000):
            if self.message is None:
                return []
            return super().get_messages(narrow, num_before)

        def send_message(self, content):
            self.sent.append(content)
            return 8

        def update_message(self, message_id, content):
            self.updated.append((message_id, content))

        def add_reaction(self, message_id, name):
            self.added.append((message_id, name))

        def remove_reaction(self, message_id, name):
            self.removed.append((message_id, name))

    STATE = {
        "state": "closed",
        "merged": True,
        "head": "h",
        "title": "Old PR",
        "author": "alice",
        "roadmaps": ["roadmap/PDE"],
    }

    def test_legacy_post_is_rewritten_in_place(self):
        old = "https://github.com/FormalFrontier/TauCeti/pull/12"
        message = {"id": 7, "sender_id": 42, "content": old, "reactions": []}
        z = self.FakeZulip(message)
        changes = zulip.reconcile(
            z, "12", create=False, ci_override=None, bot_id=42, state=self.STATE)
        self.assertEqual(changes, 2)  # content plus the terminal merge reaction
        self.assertEqual(z.updated[0][0], 7)
        self.assertIn("https://github.com/TauCetiProject/TauCeti/pull/12", z.updated[0][1])
        self.assertIn("author: [alice]", z.updated[0][1])
        self.assertIn("roadmap: PDE", z.updated[0][1])
        self.assertEqual(z.added, [(7, "merge")])

    def test_dry_run_reports_without_writing(self):
        old = "https://github.com/FormalFrontier/TauCeti/pull/12"
        message = {"id": 7, "sender_id": 42, "content": old, "reactions": []}
        z = self.FakeZulip(message)
        changes = zulip.reconcile(
            z, "12", create=False, ci_override=None, bot_id=42,
            state=self.STATE, dry_run=True)
        self.assertEqual(changes, 2)
        self.assertEqual(z.updated, [])
        self.assertEqual(z.added, [])

    def test_unreported_ci_is_yellow_but_waiting_review_has_no_review_emoji(self):
        content = zulip.pr_message_content(
            "12", self.STATE["title"], self.STATE["author"], self.STATE["roadmaps"])
        current = "https://github.com/TauCetiProject/TauCeti/pull/12"
        message = {"id": 7, "sender_id": 42, "content": content, "reactions": []}
        z = self.FakeZulip(message)
        open_state = {**self.STATE, "state": "open", "merged": False}
        status = {
            "lifecycle": "open",
            "ci": None,
            "review": "none",
            "review_inprogress": False,
            "head": "h",
            "title": "Old PR",
        }
        with mock.patch.object(zulip.core, "derive", return_value=status):
            changes = zulip.reconcile(
                z, "12", create=False, ci_override=None,
                bot_id=42, state=open_state)
        self.assertIn(current, z.searches)
        self.assertEqual(changes, 1)
        self.assertEqual(z.added, [(7, "yellow")])

    def test_label_event_self_heals_only_an_open_pr(self):
        status = {
            "lifecycle": "open",
            "ci": None,
            "review": "none",
            "review_inprogress": False,
            "head": "h",
            "title": "Old PR",
        }
        open_state = {**self.STATE, "state": "open", "merged": False}
        z = self.FakeZulip(None)
        with mock.patch.object(zulip.core, "derive", return_value=status):
            zulip.reconcile(
                z, "12", create=False, ci_override=None,
                bot_id=42, state=open_state, create_if_open=True)
        self.assertEqual(len(z.sent), 1)

        z = self.FakeZulip(None)
        changes = zulip.reconcile(
            z, "12", create=False, ci_override=None,
            bot_id=42, state=self.STATE, create_if_open=True)
        self.assertEqual(changes, 0)
        self.assertEqual(z.sent, [])


class Backfill(unittest.TestCase):
    def test_continues_and_collects_item_failures(self):
        class Z:
            def __init__(self):
                self.auth_calls = 0

            def my_user_id(self):
                self.auth_calls += 1
                return 42

        rows = [
            json.dumps({"number": 1, **Reconcile.STATE}),
            json.dumps({"number": 2, **Reconcile.STATE}),
        ]
        z = Z()
        with (
            mock.patch.object(zulip, "topic_message_index", return_value={}),
            mock.patch.object(
                zulip, "reconcile",
                side_effect=[3, RuntimeError("temporary")],
            ) as rec,
        ):
            seen, changes, failures = zulip.backfill(z, rows)
        self.assertEqual((seen, changes), (2, 3))
        self.assertEqual(failures, [("PR #2", "temporary")])
        self.assertEqual(z.auth_calls, 1)
        self.assertEqual(rec.call_count, 2)


class TopicMessageIndex(unittest.TestCase):
    def test_pages_once_and_indexes_current_and_legacy_urls(self):
        class Z:
            def __init__(self):
                self.anchors = []

            def get_message_page(self, narrow, anchor="newest", num_before=1000):
                self.anchors.append(anchor)
                if anchor == "newest":
                    return {
                        "found_oldest": False,
                        "messages": [
                            {
                                "id": 20,
                                "sender_id": 42,
                                "content": "https://github.com/TauCetiProject/TauCeti/pull/2",
                            },
                            {
                                "id": 10,
                                "sender_id": 42,
                                "content": "https://github.com/TauCetiProject/TauCeti/pull/1",
                            },
                            {
                                "id": 15,
                                "sender_id": 99,
                                "content": "https://github.com/TauCetiProject/TauCeti/pull/99",
                            },
                        ],
                    }
                return {
                    "found_oldest": True,
                    "messages": [
                        {
                            "id": 10,
                            "sender_id": 42,
                            "content": "https://github.com/TauCetiProject/TauCeti/pull/1",
                        },
                        {
                            "id": 5,
                            "sender_id": 42,
                            "content": "https://github.com/FormalFrontier/TauCeti/pull/3",
                        },
                    ],
                }

        z = Z()
        index = zulip.topic_message_index(z, 42)
        self.assertEqual(z.anchors, ["newest", 10])
        self.assertEqual({pr: message["id"] for pr, message in index.items()},
                         {"1": 10, "2": 20, "3": 5})


class Retry(unittest.TestCase):
    class Response:
        def __enter__(self):
            return self

        def __exit__(self, *args):
            return False

        def read(self):
            return b'{"result":"success"}'

    def test_rate_limit_retries_after_server_delay(self):
        error = zulip.urllib.error.HTTPError(
            "https://example.test", 429, "rate limit",
            {"Retry-After": "2.5"},
            io.BytesIO(b'{"code":"RATE_LIMIT_HIT"}'),
        )
        z = zulip.Zulip("bot@example.com", "key", "https://example.test")
        with (
            mock.patch.object(
                zulip.urllib.request, "urlopen",
                side_effect=[error, self.Response()],
            ),
            mock.patch.object(zulip, "sleep_for") as sleep,
        ):
            self.assertEqual(z._call("GET", "/messages", None)["result"], "success")
        sleep.assert_called_once_with(2.5)

    def test_send_message_does_not_retry_lost_responses(self):
        error = zulip.urllib.error.HTTPError(
            "https://example.test", 503, "unavailable", {},
            io.BytesIO(b'{"code":"TEMPORARY"}'),
        )
        z = zulip.Zulip("bot@example.com", "key", "https://example.test")
        with (
            mock.patch.object(
                zulip.urllib.request, "urlopen",
                side_effect=[error, self.Response()],
            ) as urlopen,
            mock.patch.object(zulip, "sleep_for") as sleep,
        ):
            with self.assertRaises(RuntimeError):
                z.send_message("hello")
        self.assertEqual(urlopen.call_count, 1)
        sleep.assert_not_called()


if __name__ == "__main__":
    unittest.main()
