#!/usr/bin/env python3
"""Probe for one exact, publicly readable Tau Ceti Lake cache map.

Exit successfully only when the map for the requested Git revision and Lean toolchain can be
downloaded from the anonymous read endpoint and has the JSON-lines shape Lake publishes.  Every
other result is deliberately a miss: main CI uses a miss to retain its staging/publication
fallback for direct human merges and for transient cache-service failures.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
import tempfile
import urllib.parse


REVISION = re.compile(r"\A[0-9a-f]{40}\Z")
TOOLCHAIN = re.compile(r"\Aleanprover/lean4:[0-9A-Za-z][0-9A-Za-z._+-]*\Z")
INPUT_HASH = re.compile(r"\A[0-9a-f]{16}\Z")
ARTIFACT = re.compile(r"\A[0-9a-f]{16}\.ltar\Z")


def exact_map_url(endpoint: str, toolchain: str, revision: str) -> str:
    """Return the public revision-map URL written by ``lake cache put-staged``."""
    endpoint = endpoint.strip().rstrip("/")
    parsed = urllib.parse.urlsplit(endpoint)
    if (parsed.scheme != "https" or not parsed.netloc or parsed.username is not None
            or parsed.password is not None or parsed.query or parsed.fragment):
        raise ValueError("the public revision endpoint is not a plain HTTPS URL")
    if not REVISION.fullmatch(revision):
        raise ValueError("the revision is not a lowercase 40-character Git object ID")
    if not TOOLCHAIN.fullmatch(toolchain):
        raise ValueError("the toolchain is not a leanprover/lean4 release")

    # Lake scopes toolchain-dependent caches by this escaped elan toolchain name.  Keep this in
    # sync with the confirmation URL in publish-lake-cache.yml.
    scope = toolchain.replace("/", "--").replace(":", "---")
    return (f"{endpoint}/TauCetiProject/TauCeti/tc/{scope}/{revision}.jsonl")


def valid_map(path: pathlib.Path) -> tuple[bool, str]:
    """Check enough of Lake's JSONL map shape to reject empty/error responses."""
    try:
        lines = 0
        with path.open(encoding="utf-8") as handle:
            for lines, line in enumerate(handle, start=1):
                value = json.loads(line)
                if lines == 1:
                    if not isinstance(value, str) or not value:
                        return False, "the public response has no Lake map-version header"
                elif (not isinstance(value, list) or len(value) != 2
                      or not isinstance(value[0], str) or not INPUT_HASH.fullmatch(value[0])
                      or not isinstance(value[1], str) or not ARTIFACT.fullmatch(value[1])):
                    return False, f"the public response line {lines} is not a Lake output mapping"
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        return False, f"the public response is not valid JSONL: {exc}"
    if lines < 2:
        return False, "the public response contains no root-package output mappings"
    return True, ""


def probe(endpoint: str, toolchain: str, revision: str, runner=None) -> tuple[bool, str, str]:
    """Return ``(found, url, reason)`` without turning an inconclusive probe into an error."""
    try:
        url = exact_map_url(endpoint, toolchain, revision)
    except ValueError as exc:
        return False, "", str(exc)

    runner = runner or subprocess.run
    with tempfile.TemporaryDirectory(prefix="tauceti-cache-probe-") as directory:
        destination = pathlib.Path(directory) / "outputs.jsonl"
        try:
            result = runner(
                ["curl", "--fail", "--silent", "--show-error", "--max-time", "30",
                 "--output", str(destination), url],
                capture_output=True,
                text=True,
            )
        except OSError as exc:
            return False, url, f"could not run curl: {exc}"
        if result.returncode != 0:
            detail = (result.stderr or "").strip()
            reason = f"curl exited {result.returncode}"
            return False, url, f"{reason}: {detail}" if detail else reason

        found, reason = valid_map(destination)
        return found, url, reason


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("endpoint", help="public Lake revision endpoint")
    parser.add_argument("toolchain", help="contents of lean-toolchain")
    parser.add_argument("revision", help="exact Tau Ceti Git revision")
    args = parser.parse_args(argv)

    found, url, reason = probe(args.endpoint, args.toolchain, args.revision)
    if found:
        print(f"found valid public Lake cache map: {url}")
        return 0
    print(f"no usable exact public Lake cache map: {reason}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
