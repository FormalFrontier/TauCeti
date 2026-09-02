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


def run(value: str | None, **higher: str):
    env = dict(os.environ)
    for name in ("MATHLIB_CACHE_BASE_URL", "MATHLIB_CACHE_GET_URL", "MATHLIB_CACHE_FROM"):
        env.pop(name, None)
    if value is not None:
        env["MATHLIB_CACHE_BASE_URL"] = value
    env.update(higher)
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

    print("a higher-precedence read variable is refused, not silently outranked")
    check(
        run(None, MATHLIB_CACHE_GET_URL="https://evil.invalid") != 0,
        "MATHLIB_CACHE_GET_URL set with no base is refused",
    )
    check(
        run("https://cache.mathlib.org", MATHLIB_CACHE_GET_URL="https://evil.invalid") != 0,
        "MATHLIB_CACHE_GET_URL is refused even beside an allowlisted base",
    )
    check(
        run(None, MATHLIB_CACHE_FROM="master") != 0,
        "MATHLIB_CACHE_FROM is refused",
    )
    check(
        run(None, MATHLIB_CACHE_GET_URL="", MATHLIB_CACHE_FROM="") == 0,
        "empty higher-precedence variables are not treated as set",
    )

    print("normalisation trims exactly what Char.isWhitespace does, no wider")
    for name, ch in (("space", " "), ("tab", "\t"), ("CR", "\r"), ("LF", "\n")):
        check(
            run(f"{ch}https://cache.mathlib.org{ch}") == 0,
            f"a surrounding {name} is trimmed, as trimAscii trims it",
        )
    for name, ch in (("vertical tab", "\v"), ("form feed", "\f"),
                     ("an em space", "\u2003")):
        check(
            run(f"{ch}https://cache.mathlib.org{ch}") != 0,
            f"{name} is NOT trimmed, since trimAscii keeps it and the tool would "
            f"resolve a different URL",
        )

    print("the allowlist file is parsed the way the tool would read a value")
    check(
        run("https://cache.math lib.org") != 0,
        "an entry with internal whitespace cannot be matched",
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
        check(bool(checks), f"{name}: has a check step")
        if not checks or not uses:
            continue
        # Every fetch needs a check between it and the previous fetch, not merely one check
        # somewhere earlier in the job: steps in between can append to $GITHUB_ENV, so a
        # single early check stops speaking for the environment once anything runs after it.
        # Group by enclosing step: a `run:` block that calls `cache get` and then `cache get!`
        # is one fetch for this purpose, since nothing can run between them.
        starts = [i for i, l in enumerate(lines) if re.match(r"^      - name: ", l)]

        def step_of(i: int) -> int:
            return max([j for j in starts if j <= i], default=-1)

        fetch_steps = sorted({step_of(u) for u in uses})
        check_steps = sorted({step_of(c) for c in checks})
        prev = -1
        for f in fetch_steps:
            check(
                any(prev < c < f for c in check_steps),
                f"{name}: a check guards the fetch step at line {f + 1}",
            )
            prev = f
        check(
            all(job_at(lines, u) == job for u in uses)
            and all(job_at(lines, c) == job for c in checks),
            f"{name}: the checks share the {job} job with every fetch",
        )
        check(
            f"MATHLIB_CACHE_BASE_URL: ${{{{ vars.MATHLIB_CACHE_BASE_URL }}}}" in text,
            f"{name}: exports MATHLIB_CACHE_BASE_URL from the repository variable",
        )
        check(
            "MATHLIB_CACHE_GET_URL" not in text,
            f"{name}: no longer reads the superseded MATHLIB_CACHE_GET_URL",
        )

    print("the check resolves its script path against the job's working directory")
    for name in CACHE_JOBS:
        text = (WORKFLOWS / name).read_text()
        # A job whose steps default to some other directory must be overridden on the check
        # step, or `bash scripts/check-cache-endpoint.sh` resolves against the wrong root and
        # the guard fails open with "No such file" on a path nobody looks at.
        job_default = re.search(
            r"^    defaults:\n      run:\n        working-directory: (.+)", text, re.M)
        step = re.search(
            r"^      - name: Check the Mathlib cache endpoint against the reviewed allowlist\n"
            r"(?:^ +#.*\n)*"
            r"(?:^        working-directory: (.+)\n)?"
            r"(?:^ +#.*\n)*"
            r"^        run: bash (\S+)\n",
            text, re.M)
        check(step is not None, f"{name}: the check step parses as expected")
        if step is None:
            continue
        if job_default:
            check(
                step.group(1) is not None,
                f"{name}: the check step overrides the job's "
                f"working-directory ({job_default.group(1)})",
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
