#!/usr/bin/env python3
"""Unit tests for scripts/toolchain_tags.py.

Run with: python3 scripts/test_toolchain_tags.py

No network and no git: the era walk takes its inputs as arguments, and the two facts a tag
promises are injected. The live behaviour that unit tests cannot reach, whether the cache
host answers a given client at all, is covered by a test that pins HOW it is asked rather
than what it answers, because getting that wrong made every commit look uncached.
"""

import io
import json
import os
import subprocess
import sys
import unittest
from contextlib import redirect_stdout

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import toolchain_tags as tt  # noqa: E402


class VersionNames(unittest.TestCase):
    def test_releases_and_rcs_parse(self):
        self.assertEqual(tt.parse_release("v4.33.0")[:3], (4, 33, 0))
        self.assertEqual(tt.parse_release("v4.33.0-rc2")[3], 2)

    def test_non_releases_do_not(self):
        for name in ("v2024", "v4.32.0-rc1-patch1", "nightly-2026-01-01", "", None):
            self.assertIsNone(tt.parse_release(name), name)

    def test_a_final_release_sorts_after_its_own_rcs(self):
        order = ["v4.32.1", "v4.33.0-rc1", "v4.33.0-rc2", "v4.33.0", "v4.34.0-rc1"]
        self.assertEqual(sorted(order, key=tt.release_key), order)

    def test_only_release_toolchains_name_a_release(self):
        self.assertEqual(tt.release_of_toolchain("leanprover/lean4:v4.33.0"), "v4.33.0")
        self.assertIsNone(tt.release_of_toolchain("leanprover/lean4:nightly-2026-01-01"))
        self.assertIsNone(tt.release_of_toolchain("leanprover/lean4-pr-releases:pr-1"))
        self.assertIsNone(tt.release_of_toolchain(""))


class TagMessage(unittest.TestCase):
    ROW = {"release": "v4.33.0-rc2", "toolchain": "leanprover/lean4:v4.33.0-rc2",
           "commit": "f" * 40, "mathlib_rev": "9" * 40, "status": "ready", "reason": None}

    def test_it_records_the_toolchain_the_pin_and_the_commit(self):
        message = tt.tag_message(self.ROW)
        self.assertIn("leanprover/lean4:v4.33.0-rc2", message)
        self.assertIn("9" * 40, message)
        self.assertIn("f" * 40, message)

    def test_it_does_not_claim_the_pin_is_exact(self):
        # The rule deliberately does not chase exact pins, so the message must not imply it.
        message = tt.tag_message(self.ROW)
        self.assertIn("at or after", message)
        self.assertNotIn("exactly", message)

    def test_an_unknown_pin_is_said_rather_than_shown_as_none(self):
        self.assertIn("unknown", tt.tag_message(dict(self.ROW, mathlib_rev=None)))


class CreateRefuses(unittest.TestCase):
    def test_it_will_not_tag_anything_that_is_not_ready(self):
        for status in ("blocked", "tagged", "out-of-scope"):
            row = dict(TagMessage.ROW, status=status, reason="because")
            with self.subTest(status=status), self.assertRaises(RuntimeError):
                tt.create_tag(row)

    def test_dry_run_creates_nothing_and_says_what_it_would_do(self):
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertFalse(tt.create_tag(dict(TagMessage.ROW), dry_run=True))
        self.assertIn("would tag v4.33.0-rc2", out.getvalue())


class CacheProbe(unittest.TestCase):
    """How the cache is asked, not what it answers.

    The read host answers python's default user agent with 403 and curl with 200, so a
    urllib probe reported every commit as uncached and the whole report became noise. That
    is invisible to a unit test that stubs the answer, so pin the client and the handling
    of anything that is not a clear yes or no."""

    def test_it_asks_through_curl(self):
        source = open(tt.__file__).read()
        probe = source[source.index("def cache_published"):source.index("def existing_tags")]
        self.assertIn('"curl"', probe)
        self.assertNotIn("urllib.request.urlopen", probe)

    def _with_curl(self, code, returncode=0):
        original = subprocess.run

        def fake(cmd, *a, **k):
            if cmd and cmd[0] == "curl":
                return subprocess.CompletedProcess(cmd, returncode, code, "")
            return original(cmd, *a, **k)

        self.addCleanup(setattr, subprocess, "run", original)
        subprocess.run = fake

    def test_200_is_yes_and_404_is_no(self):
        self._with_curl("200")
        self.assertTrue(tt.cache_published("leanprover/lean4:v4.33.0", "a" * 40))
        self._with_curl("404")
        self.assertFalse(tt.cache_published("leanprover/lean4:v4.33.0", "a" * 40))

    def test_anything_else_is_not_a_verdict(self):
        # A 403, a 500 or a proxy error must not quietly read as "no cache", which would
        # report a perfectly good commit as unpublishable.
        for code in ("403", "500", "000"):
            self._with_curl(code)
            with self.subTest(code=code), self.assertRaises(RuntimeError):
                tt.cache_published("leanprover/lean4:v4.33.0", "a" * 40)

    def test_the_scope_is_the_one_lake_writes(self):
        seen = {}
        original = subprocess.run

        def fake(cmd, *a, **k):
            if cmd and cmd[0] == "curl":
                seen["url"] = cmd[-1]
                return subprocess.CompletedProcess(cmd, 0, "200", "")
            return original(cmd, *a, **k)

        self.addCleanup(setattr, subprocess, "run", original)
        subprocess.run = fake
        tt.cache_published("leanprover/lean4:v4.33.0-rc2", "b" * 40)
        self.assertIn("/tc/leanprover--lean4---v4.33.0-rc2/", seen["url"])
        self.assertTrue(seen["url"].endswith("b" * 40 + ".jsonl"))


class Report(unittest.TestCase):
    ROWS = [
        {"release": "v4.32.0", "toolchain": "leanprover/lean4:v4.32.0", "commit": "1" * 40,
         "mathlib_rev": "a" * 40, "status": "out-of-scope", "reason": "predates the cache"},
        {"release": "v4.33.0-rc1", "toolchain": "leanprover/lean4:v4.33.0-rc1",
         "commit": "2" * 40, "mathlib_rev": "b" * 40, "status": "tagged", "reason": None},
        {"release": "v4.33.0-rc2", "toolchain": "leanprover/lean4:v4.33.0-rc2",
         "commit": "3" * 40, "mathlib_rev": "c" * 40, "status": "ready", "reason": None},
        {"release": "v4.34.0-rc1", "toolchain": "leanprover/lean4:v4.34.0-rc1",
         "commit": "4" * 40, "mathlib_rev": "d" * 40, "status": "blocked",
         "reason": "post-merge CI on 44444444 concluded failure"},
    ]

    def test_the_rule_is_part_of_the_output(self):
        text = tt.render(self.ROWS)
        self.assertIn("FIRST commit on `main`", text)
        self.assertIn("Tags are never moved", text)

    def test_it_names_the_command_for_each_ready_release(self):
        text = tt.render(self.ROWS)
        self.assertIn("--create v4.33.0-rc2", text)
        self.assertNotIn("--create v4.33.0-rc1", text)

    def test_it_separates_what_needs_a_human(self):
        text = tt.render(self.ROWS)
        self.assertIn("Needing a human", text)
        self.assertIn("v4.34.0-rc1: post-merge CI", text)

    def test_nothing_ready_says_so_rather_than_printing_an_empty_list(self):
        done = [dict(r, status="tagged", reason=None) for r in self.ROWS]
        self.assertIn("Nothing is ready to tag", tt.render(done))

    def test_no_instruction_ever_moves_or_deletes_a_tag(self):
        text = tt.render(self.ROWS)
        for forbidden in ("--force", "tag -f", "tag -d", "push --delete"):
            self.assertNotIn(forbidden, text)

    def test_the_json_form_is_one_row_per_release(self):
        rows = json.loads(json.dumps(self.ROWS))
        self.assertEqual(len(rows), len({r["release"] for r in rows}))
        for row in rows:
            self.assertIn(row["status"], tt.STATUSES)


class UnreachableReleases(unittest.TestCase):
    """A release main never ran on must be REPORTED, not omitted.

    The audit exists to say which releases have no tag. Walking only the toolchains main
    ran on answered a different question and left `v4.33.0`, which the daily bump stepped
    over, and the two `stable`-branch patch releases silently absent."""

    def test_a_skipped_release_is_unreachable_not_missing(self):
        row = tt._unreachable_row("v4.33.0", {})
        self.assertEqual(row["status"], "unreachable")
        self.assertIsNone(row["commit"])
        self.assertIn("never ran", row["reason"])

    def test_a_skipped_release_below_the_cutoff_is_out_of_scope(self):
        # v4.32.1 is both unreachable and older than the cache; the cache bound is the
        # more useful thing to say, since it applies to its neighbours too.
        row = tt._unreachable_row("v4.32.1", {})
        self.assertEqual(row["status"], "out-of-scope")
        self.assertIn(tt.EARLIEST_RELEASE, row["reason"])

    def _with_cache_answer(self, answer):
        original = tt.cache_published
        self.addCleanup(setattr, tt, "cache_published", original)
        def fake(toolchain, sha):
            if isinstance(answer, Exception):
                raise answer
            return answer
        tt.cache_published = fake

    def test_a_hand_made_tag_on_an_unreachable_release_is_reported_as_tagged(self):
        # A release main never ran on can still be tagged by hand off a main commit. The
        # report saying "no tag is possible" over the top of an existing tag would be the
        # tool contradicting the repository.
        self._with_cache_answer(False)
        row = tt._unreachable_row("v4.33.0", {"v4.33.0": "e" * 40})
        self.assertEqual(row["status"], "tagged")
        self.assertEqual(row["commit"], "e" * 40)
        self.assertIn("constructed by hand", row["reason"])
        self.assertNotIn("No tag is possible", tt.render([row]))

    def test_whether_a_hand_made_tag_has_a_cache_is_checked_not_assumed(self):
        # Nothing publishes for a commit off main automatically, so "no cache" is the usual
        # answer, but one can be uploaded by hand. Asserting it rather than asking made the
        # report wrong the moment that happened.
        self._with_cache_answer(True)
        self.assertIn("a Lake cache was published",
                      tt._unreachable_row("v4.33.0", {"v4.33.0": "e" * 40})["reason"])
        self._with_cache_answer(False)
        self.assertIn("no published Lake cache",
                      tt._unreachable_row("v4.33.0", {"v4.33.0": "e" * 40})["reason"])

    def test_an_unreadable_cache_is_not_reported_as_absent(self):
        self._with_cache_answer(RuntimeError("the cache answered HTTP 500"))
        self.assertIn("could not be checked",
                      tt._unreachable_row("v4.33.0", {"v4.33.0": "e" * 40})["reason"])

    def test_the_report_explains_why_no_tag_is_possible(self):
        rows = [tt._unreachable_row("v4.33.0", {})]
        text = tt.render(rows)
        self.assertIn("No tag is possible", text)
        self.assertIn("stepped over", text)
        self.assertIn("stable", text)

    def test_a_table_row_without_a_commit_renders(self):
        text = tt.render([tt._unreachable_row("v4.33.0", {})])
        self.assertIn("v4.33.0", text)

    def test_the_audit_covers_releases_main_never_ran_on(self):
        original = {name: getattr(tt, name)
                    for name in ("mathlib_releases", "eras", "existing_tags",
                                 "mathlib_pin", "ci_passed", "cache_published")}
        for name, value in original.items():
            self.addCleanup(setattr, tt, name, value)
        tt.mathlib_releases = lambda: ["v4.33.0-rc1", "v4.33.0", "v4.34.0-rc1"]
        tt.eras = lambda ref=None: [
            {"release": "v4.33.0-rc1", "toolchain": "leanprover/lean4:v4.33.0-rc1",
             "commit": "a" * 40, "index": 1},
            {"release": "v4.34.0-rc1", "toolchain": "leanprover/lean4:v4.34.0-rc1",
             "commit": "b" * 40, "index": 2},
        ]
        tt.existing_tags = lambda: {"v4.33.0-rc1": "a" * 40}
        tt.mathlib_pin = lambda sha: "c" * 40
        tt.ci_passed = lambda sha: "success"
        tt.cache_published = lambda toolchain, sha: True
        rows = {r["release"]: r["status"] for r in tt.audit()}
        self.assertEqual(rows, {"v4.33.0-rc1": "tagged", "v4.33.0": "unreachable",
                                "v4.34.0-rc1": "ready"})


class CommandLine(unittest.TestCase):
    def test_create_without_a_release_or_all_is_an_error(self):
        original = tt.audit
        tt.audit = lambda *a, **k: []
        self.addCleanup(setattr, tt, "audit", original)
        with self.assertRaises(SystemExit):
            tt.main(["--create"])

    def test_the_help_carries_the_rule(self):
        out = io.StringIO()
        with redirect_stdout(out), self.assertRaises(SystemExit):
            tt.main(["--help"])
        self.assertIn("FIRST commit on `main`", out.getvalue())


if __name__ == "__main__":
    unittest.main()
