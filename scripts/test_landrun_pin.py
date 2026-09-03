"""Ensure every workflow that runs code under landrun trusts the same binary.

Run with: python3 scripts/test_landrun_pin.py

pr-build.yml sandboxes untrusted PR sources; nightly-verify.yml sandboxes a cache-restored
build that imports the artifacts it is judging. Both pin the landrun release and its SHA-256,
and both would be weakened by trusting a different binary than the other.

The pin is deliberately duplicated rather than shared through a composite action: pr-build.yml
sits on the merge queue's critical path and runs from the base definition under
pull_request_target, so a shared action could not be exercised by the PR that introduced it.
This test is what stops the copies drifting.
"""

import pathlib
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
WORKFLOWS = (
    ROOT / ".github/workflows/pr-build.yml",
    ROOT / ".github/workflows/nightly-verify.yml",
)
SHA = re.compile(r"^\s*LANDRUN_SHA256:\s*([0-9a-f]{64})\s*$", re.MULTILINE)
VER = re.compile(r"^\s*LANDRUN_VER:\s*(v[0-9][0-9A-Za-z.\-]*)\s*$", re.MULTILINE)


class LandrunPin(unittest.TestCase):
    def test_every_sandboxing_workflow_pins_the_same_landrun(self):
        seen = {}
        for workflow in WORKFLOWS:
            text = workflow.read_text()
            shas, vers = SHA.findall(text), VER.findall(text)
            self.assertEqual(len(shas), 1, f"expected one LANDRUN_SHA256 in {workflow.name}")
            self.assertEqual(len(vers), 1, f"expected one LANDRUN_VER in {workflow.name}")
            seen[workflow.name] = (vers[0], shas[0])
        distinct = set(seen.values())
        self.assertEqual(
            len(distinct), 1,
            "workflows disagree on which landrun to trust: "
            + ", ".join(f"{name} pins {ver} {sha}" for name, (ver, sha) in sorted(seen.items())),
        )

    def test_every_sandboxing_workflow_verifies_the_checksum(self):
        # A pin that is downloaded but never checked is not a pin.
        for workflow in WORKFLOWS:
            with self.subTest(workflow=workflow.name):
                self.assertIn('echo "${LANDRUN_SHA256}  landrun" | sha256sum -c -',
                              workflow.read_text())


if __name__ == "__main__":
    unittest.main()
