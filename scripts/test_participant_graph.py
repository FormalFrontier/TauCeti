#!/usr/bin/env python3
"""Tests for the participation snapshot graph.

Run with:

    PYTHONPATH=scripts python3 scripts/test_participant_graph.py
"""

import json
import pathlib
import tempfile
import unittest
import xml.etree.ElementTree as ET
from unittest import mock

import participant_graph as pg


class ParticipantGraphTest(unittest.TestCase):
    def test_filters_bot_suffixes_and_app_aliases(self):
        self.assertIsNone(pg.canonical_human("github-actions[bot]"))
        self.assertIsNone(pg.canonical_human("tauceti-review-bot"))
        self.assertIsNone(pg.canonical_human("Copilot"))
        self.assertIsNone(pg.canonical_human("claude"))
        self.assertEqual(pg.canonical_human("CBirkbeck"), "cbirkbeck")

    def test_extracts_authors_and_participants(self):
        page = {
            "data": {"repository": {"pullRequests": {
                "nodes": [{
                    "number": 7,
                    "author": {"login": "HumanAuthor"},
                    "participants": {
                        "nodes": [
                            {"login": "HumanReviewer"},
                            {"login": "github-actions[bot]"},
                        ],
                        "pageInfo": {"hasNextPage": False},
                    },
                }],
                "pageInfo": {"hasNextPage": True, "endCursor": "next"},
            }}},
        }

        people, has_next, cursor = pg.actors_from_page(
            page, "pullRequests", "owner/repo"
        )

        self.assertEqual(people, {"humanauthor", "humanreviewer"})
        self.assertTrue(has_next)
        self.assertEqual(cursor, "next")

    def test_refuses_to_undercount_large_conversations(self):
        page = {
            "data": {"repository": {"issues": {
                "nodes": [{
                    "number": 9,
                    "author": {"login": "person"},
                    "participants": {
                        "nodes": [],
                        "pageInfo": {"hasNextPage": True},
                    },
                }],
                "pageInfo": {"hasNextPage": False, "endCursor": None},
            }}},
        }

        with self.assertRaisesRegex(RuntimeError, "more than 100 participants"):
            pg.actors_from_page(page, "issues", "owner/repo")

    def test_connection_paginates_with_raw_cursor(self):
        def page(login, has_next, cursor):
            return {
                "data": {"repository": {"issues": {
                    "nodes": [{
                        "number": 1,
                        "author": {"login": login},
                        "participants": {
                            "nodes": [],
                            "pageInfo": {"hasNextPage": False},
                        },
                    }],
                    "pageInfo": {
                        "hasNextPage": has_next,
                        "endCursor": cursor,
                    },
                }}},
            }

        with mock.patch.object(
            pg, "gh_json",
            side_effect=[page("First", True, "opaque-cursor"), page("Second", False, None)],
        ) as query:
            people = pg.fetch_connection("owner/repo", "issues")

        self.assertEqual(people, {"first", "second"})
        second_args = query.call_args_list[1].args
        self.assertIn("cursor=opaque-cursor", second_args)
        self.assertEqual(second_args[second_args.index("cursor=opaque-cursor") - 1], "-f")

    def test_contributors_keep_linked_humans_only(self):
        payload = [[
            {"login": "Human", "type": "User"},
            {"login": "github-actions[bot]", "type": "Bot"},
            {"name": "Unlinked Human", "email": "human@example.com", "type": "Anonymous"},
        ]]
        with mock.patch.object(pg, "gh_json", return_value=payload):
            people = pg.fetch_contributors("owner/repo")

        self.assertEqual(people, {"human"})

    def test_loads_filters_and_renders_snapshot(self):
        repositories = {
            repo: ["SharedHuman", f"{label}Human", "Copilot"]
            for repo, label, _ in pg.REPOSITORIES
        }
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = pathlib.Path(tmp)
            data = tmp_path / "people.json"
            out = tmp_path / "people.svg"
            data.write_text(json.dumps({
                "generatedAt": "2026-07-29",
                "repositories": repositories,
            }))

            people, generated = pg.load_data(str(data))
            total = pg.render(people, "Participation", str(out), generated)
            svg = out.read_text()
            ET.fromstring(svg)

        self.assertEqual(total, 5)
        self.assertIn('class="total" x="50" y="91">5</text>', svg)
        self.assertIn("TauCetiRoadmap", svg)
        self.assertIn("2026-07-29", svg)
        self.assertIn("Multi-repo participants appear in each bar", svg)
        self.assertIn("<desc ", svg)

    def test_dump_and_load_round_trip(self):
        people = {
            repo: {"shared", label.casefold()}
            for repo, label, _ in pg.REPOSITORIES
        }
        with tempfile.TemporaryDirectory() as tmp:
            data = pathlib.Path(tmp) / "people.json"
            pg.dump_data(str(data), people, "2026-07-29")
            loaded, generated = pg.load_data(str(data))

        self.assertEqual(loaded, people)
        self.assertEqual(generated, "2026-07-29")


if __name__ == "__main__":
    unittest.main()
