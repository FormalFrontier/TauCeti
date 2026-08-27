#!/usr/bin/env python3
"""Regression tests for main's exact public Lake cache-map probe."""

import pathlib
import subprocess
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import lake_cache_probe as cache_probe  # noqa: E402


ROOT = pathlib.Path(__file__).resolve().parent.parent
CI = ROOT / ".github/workflows/ci.yml"
SHA = "a" * 40
TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
ENDPOINT = "https://cache.taucetiproject.org/revisions"


def response(body: str, returncode: int = 0, stderr: str = ""):
    """A curl runner that writes ``body`` to the command's requested output path."""
    def run(command, **_kwargs):
        pathlib.Path(command[command.index("--output") + 1]).write_text(body)
        return subprocess.CompletedProcess(command, returncode, "", stderr)

    return run


class ExactMapProbe(unittest.TestCase):
    def test_url_is_the_exact_lake_toolchain_and_revision_scope(self):
        url = cache_probe.exact_map_url(ENDPOINT + "/", TOOLCHAIN, SHA)
        self.assertEqual(
            url,
            ENDPOINT + "/TauCetiProject/TauCeti/tc/"
            "leanprover--lean4---v4.34.0-rc1/" + SHA + ".jsonl",
        )

    def test_only_a_downloaded_valid_map_is_a_hit(self):
        found, _url, reason = cache_probe.probe(
            ENDPOINT, TOOLCHAIN, SHA,
            response('"2026-03-17"\n["44b76000326a96d8","40b5fb725e1abfb8.ltar"]\n'),
        )
        self.assertTrue(found, reason)

    def test_a_curl_failure_is_an_inconclusive_miss(self):
        found, _url, reason = cache_probe.probe(
            ENDPOINT, TOOLCHAIN, SHA, response("", 22, "HTTP 404"),
        )
        self.assertFalse(found)
        self.assertIn("curl exited 22", reason)

    def test_an_error_page_or_empty_map_is_a_miss(self):
        for body in ("upstream error\n", '"2026-03-17"\n',
                     '{"error":"upstream"}\n{"detail":"unavailable"}\n'):
            with self.subTest(body=body):
                found, _url, _reason = cache_probe.probe(
                    ENDPOINT, TOOLCHAIN, SHA, response(body),
                )
                self.assertFalse(found)

    def test_untrusted_path_components_cannot_enter_the_url(self):
        for toolchain, revision in (("../../secret", SHA), (TOOLCHAIN, "../" + SHA)):
            with self.subTest(toolchain=toolchain, revision=revision):
                found, url, _reason = cache_probe.probe(
                    ENDPOINT, toolchain, revision, response(""),
                )
                self.assertFalse(found)
                self.assertEqual(url, "")


def step(workflow: str, name: str) -> str:
    marker = f"      - name: {name}\n"
    start = workflow.index(marker)
    end = workflow.find("\n      - name:", start + len(marker))
    return workflow[start:end if end >= 0 else None]


class MainWorkflowFallback(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.workflow = CI.read_text()

    def test_probe_defaults_to_publish_and_uses_the_public_exact_identity(self):
        block = step(self.workflow, "Probe for this exact cache on the public endpoint")
        self.assertIn("id: exact_cache", block)
        self.assertIn("steps.cachecfg.outputs.enabled == 'true'", block)
        self.assertIn("vars.LAKE_CACHE_REVISION_ENDPOINT_PUBLIC", block)
        self.assertIn("REVISION: ${{ github.sha }}", block)
        self.assertIn("python3 scripts/lake_cache_probe.py", block)
        self.assertLess(block.index('echo "exists=false"'),
                        block.index("python3 scripts/lake_cache_probe.py"))
        self.assertLess(block.index("python3 scripts/lake_cache_probe.py"),
                        block.index('echo "exists=true"'))

    def test_only_a_probe_hit_suppresses_the_existing_staging_fallback(self):
        block = step(self.workflow, "Stage TauCeti's oleans for the publish job")
        self.assertIn("steps.cachecfg.outputs.enabled == 'true'", block)
        self.assertIn("steps.exact_cache.outputs.exists != 'true'", block)
        self.assertIn('echo "staged=true"', block)
        self.assertIn("if: ${{ needs.build.outputs.staged == 'true' }}", self.workflow)


if __name__ == "__main__":
    unittest.main()
