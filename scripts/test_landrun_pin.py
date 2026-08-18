"""Ensure every workflow that runs code under landrun trusts the same binary.

Run with: python3 scripts/test_landrun_pin.py

Four workflows sandbox with landrun: pr-build.yml around untrusted PR sources, ci.yml around
main's own build and its cache staging, nightly-verify.yml around a cache-restored build that
imports the artifacts it is judging, and pr-profile.yml around its measurements. Each pins a
landrun release and its SHA-256, and each would be weakened by trusting a different binary than
the others.

The pin is deliberately duplicated rather than shared through a composite action: pr-build.yml
sits on the merge queue's critical path and runs from the base definition under
pull_request_target, so a shared action could not be exercised by the PR that introduced it and a
mistake in it would redden every PR build. This test is what stops the copies drifting.

The set of workflows is DISCOVERED rather than listed, so a fifth one cannot be added without
being covered, and the canary below keeps the four we know about from dropping out of the set
unnoticed. A workflow counts as sandboxing if `landrun` appears in it outside a comment.
"""

import pathlib
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
WORKFLOW_DIR = ROOT / ".github/workflows"

# Any `landrun` token on a line that is not a comment. Deliberately broad and fail-closed:
# matching only commands at the start of a line would let `exec landrun`, `( landrun ... )`,
# `if landrun ...` or a variable-prefixed invocation add a fifth sandboxing workflow that this
# test silently did not cover. A false positive costs a pin declaration; a false negative costs
# the guarantee.
INVOKES = re.compile(r"^(?!\s*#).*\blandrun\b", re.MULTILINE)
SHA = re.compile(r"^\s*LANDRUN_SHA256:\s*([0-9a-f]{64})\s*$", re.MULTILINE)
VER = re.compile(r"^\s*LANDRUN_VER:\s*(v[0-9][0-9A-Za-z.\-]*)\s*$", re.MULTILINE)
VERIFIES = 'echo "${LANDRUN_SHA256}  landrun" | sha256sum -c -'


def sandboxing_workflows():
    return sorted(
        (w for w in WORKFLOW_DIR.glob("*.yml") if INVOKES.search(w.read_text())),
        key=lambda w: w.name,
    )


class LandrunPin(unittest.TestCase):
    def test_the_discovery_finds_the_workflows_we_know_about(self):
        # A canary: if landrun sandboxing is removed from one of these, or the invocation is
        # reworded past the pattern above, the rest of this file would silently stop checking it.
        found = {w.name for w in sandboxing_workflows()}
        self.assertLessEqual(
            {"pr-build.yml", "ci.yml", "nightly-verify.yml", "pr-profile.yml"}, found,
            f"a workflow that used to run landrun no longer appears to; found {sorted(found)}",
        )

    def test_every_sandboxing_workflow_pins_the_same_landrun(self):
        seen = {}
        for workflow in sandboxing_workflows():
            text = workflow.read_text()
            shas, vers = SHA.findall(text), VER.findall(text)
            self.assertEqual(len(shas), 1, f"expected one LANDRUN_SHA256 in {workflow.name}")
            self.assertEqual(len(vers), 1, f"expected one LANDRUN_VER in {workflow.name}")
            seen[workflow.name] = (vers[0], shas[0])
        self.assertEqual(
            len(set(seen.values())), 1,
            "workflows disagree on which landrun to trust: "
            + ", ".join(f"{name} pins {ver} {sha}" for name, (ver, sha) in sorted(seen.items())),
        )

    def test_every_sandboxing_workflow_verifies_the_checksum(self):
        # A pin that is downloaded but never checked is not a pin.
        for workflow in sandboxing_workflows():
            with self.subTest(workflow=workflow.name):
                self.assertIn(VERIFIES, workflow.read_text())


if __name__ == "__main__":
    unittest.main()
