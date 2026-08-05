#!/usr/bin/env python3
"""Regression tests for the lines-of-code graph.

Run with:

    python3 scripts/test_loc_graph.py
"""

import os
import pathlib
import subprocess
import tempfile
import unittest

import loc_graph


def git(repo: pathlib.Path, *args: str, env=None) -> None:
    subprocess.run(
        ["git", "-C", str(repo), *args],
        check=True,
        env=env,
        stdout=subprocess.DEVNULL,
    )


class SeriesTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = pathlib.Path(self.tmp.name)
        self.env = os.environ.copy()
        self.env.update({
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_CONFIG_SYSTEM": os.devnull,
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_TERMINAL_PROMPT": "0",
        })
        git(self.repo, "init", "--quiet", "--initial-branch=main", env=self.env)
        git(self.repo, "config", "user.name", "Test", env=self.env)
        git(self.repo, "config", "user.email", "test@example.com", env=self.env)

    def tearDown(self):
        self.tmp.cleanup()

    def commit(self, author_time: str, committer_time: str, lines: int) -> None:
        source = self.repo / "Tracked.lean"
        source.write_text("example : True := by trivial\n" * lines)
        git(self.repo, "add", "Tracked.lean", env=self.env)
        env = self.env.copy()
        env["GIT_AUTHOR_DATE"] = author_time
        env["GIT_COMMITTER_DATE"] = committer_time
        git(self.repo, "commit", "--quiet", "--no-verify",
            "-m", f"{lines} lines", env=env)

    def test_uses_committer_dates(self):
        self.commit("2026-06-02T12:00:00+0000",
                    "2026-06-03T12:00:00+0000", 1)

        data = loc_graph.series(str(self.repo), ["Tracked.lean"], "HEAD")

        self.assertEqual(data, [("2026-06-03", 1)])

    def test_normalizes_committer_dates_to_utc(self):
        # These commits have decreasing local calendar dates but increasing UTC
        # timestamps, reproducing the timezone form of the graph reversal.
        self.commit("2026-07-20T00:15:00+1000",
                    "2026-07-20T00:15:00+1000", 1)
        self.commit("2026-07-19T15:00:00+0000",
                    "2026-07-19T15:00:00+0000", 2)

        data = loc_graph.series(str(self.repo), ["Tracked.lean"], "HEAD")

        self.assertEqual(data, [("2026-07-19", 2)])

    def test_last_commit_of_the_day_wins(self):
        self.commit("2026-06-02T10:00:00+0000",
                    "2026-06-02T10:00:00+0000", 1)
        self.commit("2026-06-03T10:00:00+0000",
                    "2026-06-03T10:00:00+0000", 5)
        self.commit("2026-06-03T11:00:00+0000",
                    "2026-06-03T11:00:00+0000", 3)

        data = loc_graph.series(str(self.repo), ["Tracked.lean"], "HEAD")

        self.assertEqual(data, [("2026-06-02", 1), ("2026-06-03", 3)])


if __name__ == "__main__":
    unittest.main()
