"""Who gets admitted to the claim namespace, and which leases are safe to delete.

Run with: python3 scripts/test_claims_access.py
"""

import json
import unittest
from types import SimpleNamespace
from unittest import mock

import claims_access as ca


class HumanAuthors(unittest.TestCase):
    def test_bots_never_get_the_claim_namespace(self):
        prs = [
            {"author": {"login": "alice", "is_bot": False}},
            {"author": {"login": "tauceti-review", "is_bot": True}},
            {"author": {"login": "dependabot[bot]"}},
        ]
        self.assertEqual(ca.human_authors(prs), {"alice"})

    def test_authors_are_distinct_and_deleted_accounts_are_skipped(self):
        prs = [
            {"author": {"login": "alice"}},
            {"author": {"login": "alice"}},
            {"author": None},
            {"author": {"login": ""}},
            {},
        ]
        self.assertEqual(ca.human_authors(prs), {"alice"})

    def test_no_merged_prs_admits_nobody(self):
        self.assertEqual(ca.human_authors([]), set())
        self.assertEqual(ca.human_authors(None), set())


class HasAccess(unittest.TestCase):
    """Access inherited from the organization is invisible to the collaborator list this App can see,
    so without an explicit check every org member is a candidate to invite on every single run."""

    def answer(self, returncode, stdout):
        return lambda args, token, check=True: SimpleNamespace(returncode=returncode, stdout=stdout, stderr="")

    def test_anyone_who_can_already_push_is_left_alone(self):
        for permission in ("admin", "maintain", "write"):
            with self.subTest(permission=permission), mock.patch.object(ca, "gh", self.answer(0, permission + "\n")):
                self.assertTrue(ca.has_access("an-org-member"))

    def test_read_only_or_no_access_still_needs_an_invitation(self):
        for permission in ("read", "none", ""):
            with self.subTest(permission=permission), mock.patch.object(ca, "gh", self.answer(0, permission + "\n")):
                self.assertFalse(ca.has_access("a-contributor"))

    def test_an_unreadable_answer_falls_towards_inviting(self):
        # A redundant invitation is a no-op; a missed one is a fleet that never coordinates.
        with mock.patch.object(ca, "gh", self.answer(1, "")):
            self.assertFalse(ca.has_access("a-contributor"))


class Sweepable(unittest.TestCase):
    def lease(self, expires_at):
        return json.dumps({"schema": "tauceti-claim/v1", "owner": "w1", "expires_at": expires_at})

    def test_a_live_lease_is_never_swept(self):
        self.assertFalse(ca.is_sweepable(self.lease(2000), 1000))

    def test_a_lease_inside_the_grace_period_is_never_swept(self):
        # Expired, but only just: a worker may be taking it over right now, and that takeover is a
        # CAS the sweep must not race.
        self.assertFalse(ca.is_sweepable(self.lease(1001), 1000))

    def test_a_long_expired_lease_is_swept(self):
        self.assertTrue(ca.is_sweepable(self.lease(500), 1000))

    def test_an_unreadable_lease_is_left_alone(self):
        # Anything in this namespace that we cannot parse was not written by a worker we understand,
        # so deleting it would be guessing.
        for junk in ("", "not json", "[]", '"a string"', json.dumps({"owner": "w1"})):
            with self.subTest(junk=junk):
                self.assertFalse(ca.is_sweepable(junk, 1000))

    def test_a_non_numeric_expiry_is_left_alone(self):
        for expires in ("soon", None, True, {"at": 1}):
            with self.subTest(expires=expires):
                self.assertFalse(ca.is_sweepable(self.lease(expires), 1000))


if __name__ == "__main__":
    unittest.main()
