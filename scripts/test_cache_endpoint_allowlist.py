#!/usr/bin/env python3
"""Tests for the Mathlib cache endpoint allowlist and its wiring.

The properties that matter:

* an unset or empty value is allowed -- that is the no-configuration state, and the cache
  tool treats empty as unset, so refusing it would break every build that sets nothing;
* an allowlisted value is accepted after the same normalisation the cache tool applies, so
  the check judges the string the tool will actually read;
* anything else fails, including the near-misses a prefix or suffix rule would admit;
* every workflow that fetches the Mathlib cache runs the check first, from its trusted
  checkout, and none still reads the superseded `MATHLIB_CACHE_GET_URL`.

Run: python3 scripts/test_cache_endpoint_allowlist.py
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHECK = ROOT / "scripts" / "check-cache-endpoint.sh"
WORKFLOWS = ROOT / ".github" / "workflows"

# Workflow -> the job whose steps fetch the Mathlib cache.
CACHE_JOBS = {
    "ci.yml": "build",
    "nightly-verify.yml": "verify",
    "pages.yml": "build-site",
    "pr-profile.yml": "performance-gate",
    "pr-build.yml": "sandboxed-build",
}

failures: list[str] = []


def check(cond: bool, what: str) -> None:
    print(("  ok   " if cond else "  FAIL ") + what)
    if not cond:
        failures.append(what)


def run(value: str | None):
    env = dict(os.environ)
    env.pop("MATHLIB_CACHE_BASE_URL", None)
    if value is not None:
        env["MATHLIB_CACHE_BASE_URL"] = value
    return subprocess.run(
        ["bash", str(CHECK)], env=env, capture_output=True, text=True
    ).returncode


def job_at(lines: list[str], index: int) -> str | None:
    job = None
    for i, line in enumerate(lines[:index]):
        if re.match(r"^  [a-z0-9_-]+:$", line):
            job = line.strip().rstrip(":")
    return job


def main() -> None:
    print("no configuration is allowed")
    check(run(None) == 0, "unset is accepted")
    check(run("") == 0, "empty is accepted (the tool reads empty as unset)")
    check(run("   ") == 0, "whitespace-only is accepted")

    print("an allowlisted endpoint is accepted, normalised as the cache tool normalises")
    check(run("https://cache.mathlib.org") == 0, "the exact allowlisted value is accepted")
    check(run("https://cache.mathlib.org/") == 0, "a trailing slash is accepted")
    check(run(" https://cache.mathlib.org ") == 0, "surrounding whitespace is accepted")

    print("anything else fails, including the shapes a looser rule would admit")
    check(run("https://evil.invalid") != 0, "an unrelated host is refused")
    check(
        run("https://cache.mathlib.org.evil.invalid") != 0,
        "a host that merely starts with an allowlisted one is refused",
    )
    check(
        run("https://evil.invalid/cache.mathlib.org") != 0,
        "an allowlisted string appearing in the path is refused",
    )
    check(run("http://cache.mathlib.org") != 0, "a plaintext downgrade is refused")
    check(
        run("https://cache.mathlib.org/mathlib4") != 0,
        "a container path is refused (a base URL names the host alone)",
    )

    print("every cache-fetching job checks before it fetches")
    for name, job in CACHE_JOBS.items():
        text = (WORKFLOWS / name).read_text()
        lines = text.split("\n")
        checks = [i for i, l in enumerate(lines) if "check-cache-endpoint.sh" in l]
        uses = [
            i for i, l in enumerate(lines)
            if "lake exe cache get" in l and not l.strip().startswith("#")
        ]
        check(len(checks) == 1, f"{name}: has exactly one check step")
        if len(checks) != 1 or not uses:
            continue
        check(
            all(checks[0] < u for u in uses),
            f"{name}: the check precedes every `lake exe cache get`",
        )
        check(
            all(job_at(lines, u) == job for u in uses)
            and job_at(lines, checks[0]) == job,
            f"{name}: the check shares the {job} job with every fetch",
        )
        check(
            f"MATHLIB_CACHE_BASE_URL: ${{{{ vars.MATHLIB_CACHE_BASE_URL }}}}" in text,
            f"{name}: exports MATHLIB_CACHE_BASE_URL from the repository variable",
        )
        check(
            "MATHLIB_CACHE_GET_URL" not in text,
            f"{name}: no longer reads the superseded MATHLIB_CACHE_GET_URL",
        )

    print("the PR-facing workflows validate with their trusted checkout, not the candidate's")
    for name, prefix in (("pr-build.yml", "gate/"), ("pr-profile.yml", "gate/"),
                         ("nightly-verify.yml", "fresh/")):
        text = (WORKFLOWS / name).read_text()
        check(
            f"bash {prefix}scripts/check-cache-endpoint.sh" in text,
            f"{name}: runs {prefix}scripts/check-cache-endpoint.sh",
        )

    if failures:
        print(f"\n{len(failures)} check(s) failed")
        sys.exit(1)
    print("\ncache endpoint allowlist checks passed")


if __name__ == "__main__":
    main()
