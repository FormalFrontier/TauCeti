"""Ensure reusable TauCetiReview workflows execute their pinned checkout.

Run with: python3 scripts/test_workflow_pins.py
"""

import pathlib
import re
import unittest


ROOT = pathlib.Path(__file__).resolve().parent.parent
WORKFLOWS = (
    ROOT / ".github/workflows/auto-merge.yml",
    ROOT / ".github/workflows/merge-sweep.yml",
    ROOT / ".github/workflows/review.yml",
)
CALL_PIN = re.compile(
    r"uses:\s+TauCetiProject/TauCetiReview/\.github/workflows/[^@\s]+@([0-9a-f]{40})"
)
CHECKOUT_PIN = re.compile(r"^\s+review_ref:\s+([0-9a-f]{40})\s*$", re.MULTILINE)


class WorkflowPins(unittest.TestCase):
    def test_workflow_and_checkout_pins_match(self):
        for workflow in WORKFLOWS:
            with self.subTest(workflow=workflow.name):
                text = workflow.read_text()
                call = CALL_PIN.findall(text)
                checkout = CHECKOUT_PIN.findall(text)
                self.assertEqual(len(call), 1, f"expected one pinned reusable call in {workflow}")
                self.assertEqual(len(checkout), 1, f"expected one review_ref in {workflow}")
                self.assertEqual(
                    call[0],
                    checkout[0],
                    f"{workflow.name} runs one TauCetiReview SHA but checks out another",
                )


if __name__ == "__main__":
    unittest.main()
