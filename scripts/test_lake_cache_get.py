#!/usr/bin/env python3
"""Behavioural tests for scripts/lake-cache-get.sh and its pr-build wiring.

The properties that matter are not the literal values in the workflow but these:

* a caller that says the lookup cannot hit skips it and still leaves the build
  configured for no cache -- the enable lines an earlier step wrote must be undone,
  or the build reads an enabled-but-empty cache and every module becomes a failure;
* without that signal the lookup still runs, so an unresolved merge base degrades to
  the old behaviour rather than to a silent skip;
* a miss leaves the build in exactly the same state as the skip;
* only `lean-toolchain` sets the signal -- a manifest-only bump keeps the toolchain
  and can still hit.

Run: python3 scripts/test_lake_cache_get.py
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "lake-cache-get.sh"
PR_BUILD = ROOT / ".github" / "workflows" / "pr-build.yml"

DISABLE_LINES = {
    "LAKE_ARTIFACT_CACHE=false",
    "LAKE_RESTORE_ARTIFACTS=false",
    "LAKE_CACHE_DIR=",
}

failures: list[str] = []


def check(cond: bool, what: str) -> None:
    if cond:
        print(f"  ok   {what}")
    else:
        print(f"  FAIL {what}")
        failures.append(what)


def run_script(*, skip: bool, lake_output: str, lake_rc: int):
    """Run the script against a stub `lake`. Returns (rc, github_env, lake_ran, cache_left)."""
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        cache = tmp / "pr" / ".lake" / "cache" / "revisions"
        cache.mkdir(parents=True)
        (cache / "stale.jsonl").write_text("stale\n")

        binx = tmp / "bin"
        binx.mkdir()
        marker = tmp / "lake-ran"
        (binx / "lake").write_text(
            "#!/usr/bin/env bash\n"
            f'echo ran >> "{marker}"\n'
            f"cat <<'OUT'\n{lake_output}\nOUT\n"
            f"exit {lake_rc}\n"
        )
        (binx / "lake").chmod(0o755)

        env = dict(os.environ)
        env["PATH"] = f"{binx}:{env['PATH']}"
        env["GITHUB_ENV"] = str(tmp / "github_env")
        env["RUNNER_TEMP"] = str(tmp)
        env["PUBLIC_ARTIFACT_ENDPOINT"] = "https://example.invalid/artifacts"
        env["PUBLIC_REVISION_ENDPOINT"] = "https://example.invalid/revisions"
        env.pop("LAKE_CACHE_SKIP", None)
        if skip:
            env["LAKE_CACHE_SKIP"] = "1"
        Path(env["GITHUB_ENV"]).write_text("")

        proc = subprocess.run(
            ["bash", str(SCRIPT), "pr"],
            cwd=tmp, env=env, capture_output=True, text=True,
        )
        return (
            proc.returncode,
            Path(env["GITHUB_ENV"]).read_text(),
            marker.exists(),
            (tmp / "pr" / ".lake" / "cache").exists(),
        )


def main() -> None:
    print("skip requested: the lookup is not attempted, and the build gets no cache")
    rc, gh_env, lake_ran, cache_left = run_script(skip=True, lake_output="", lake_rc=0)
    check(rc == 0, "exits 0 so the caller's build proceeds")
    check(not lake_ran, "never invokes lake")
    check(not cache_left, "discards any cache directory it was handed")
    for line in sorted(DISABLE_LINES):
        check(line in gh_env.splitlines(), f"writes {line!r} to $GITHUB_ENV")

    print("no skip: the lookup still runs, so 'unknown' degrades to looking")
    rc, gh_env, lake_ran, _ = run_script(
        skip=False, lake_output="error: no outputs found", lake_rc=1)
    check(lake_ran, "invokes lake when LAKE_CACHE_SKIP is unset")

    print("a miss leaves the build in the same state as a skip")
    check(
        DISABLE_LINES.issubset(set(gh_env.splitlines())),
        "a total miss disables the cache exactly as the skip does",
    )

    print("pr-build wires the signal from the toolchain, not from either pin")
    wf = PR_BUILD.read_text()
    check(
        re.search(r"LAKE_CACHE_SKIP:\s*\$\{\{\s*env\.TOOLCHAIN_CHANGED\s*==\s*'1'", wf)
        is not None,
        "LAKE_CACHE_SKIP is driven by TOOLCHAIN_CHANGED",
    )
    check(
        re.search(r'if \[ "\$f" = "lean-toolchain" \]; then toolchain_changed=1; fi', wf)
        is not None,
        "only lean-toolchain sets toolchain_changed (a manifest bump can still hit)",
    )
    check(
        'echo "TOOLCHAIN_CHANGED=1" >> "$GITHUB_ENV"' in wf,
        "the scope guard exports TOOLCHAIN_CHANGED",
    )

    if failures:
        print(f"\n{len(failures)} check(s) failed")
        sys.exit(1)
    print("\nlake-cache-get behaviour checks passed")


if __name__ == "__main__":
    main()
