#!/usr/bin/env python3
"""Tests for how pr-build sizes the Lake cache lookup, and for the script that runs it.

The properties that matter:

* a candidate that moves `lean-toolchain` asks about HEAD alone. The maps are keyed by
  toolchain, so no ancestor can hold a usable one -- but HEAD can, when a merge-group
  re-run meets the outputs its own earlier build published, and that case must still hit
  rather than recompile;
* every other candidate keeps a walk, bounded only as a backstop;
* only `lean-toolchain` decides this. A manifest-only bump keeps the toolchain, so its
  ancestors remain usable;
* the signal is set only when the comparison was actually made, so an unreadable tree
  entry falls through to the walk;
* whatever the caller asks for reaches Lake.

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
PR_BUILD = (ROOT / ".github" / "workflows" / "pr-build.yml").read_text()

failures: list[str] = []


def check(cond: bool, what: str) -> None:
    print(("  ok   " if cond else "  FAIL ") + what)
    if not cond:
        failures.append(what)


def lake_argv(max_revs: str) -> str:
    """Run the fetch script against a stub `lake`; return the argv it was called with."""
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        (tmp / "pr" / ".lake" / "cache").mkdir(parents=True)
        binx = tmp / "bin"
        binx.mkdir()
        argv = tmp / "argv"
        (binx / "lake").write_text(
            "#!/usr/bin/env bash\n"
            f'printf "%s\\n" "$*" >> "{argv}"\n'
            "echo 'error: no outputs found'\nexit 1\n"
        )
        (binx / "lake").chmod(0o755)
        env = dict(os.environ)
        env.update(
            PATH=f"{binx}:{env['PATH']}",
            GITHUB_ENV=str(tmp / "gh_env"),
            RUNNER_TEMP=str(tmp),
            PUBLIC_ARTIFACT_ENDPOINT="https://example.invalid/a",
            PUBLIC_REVISION_ENDPOINT="https://example.invalid/r",
            LAKE_CACHE_MAX_REVS=max_revs,
        )
        Path(env["GITHUB_ENV"]).write_text("")
        subprocess.run(["bash", str(SCRIPT), "pr"], cwd=tmp, env=env,
                       capture_output=True, text=True)
        return argv.read_text() if argv.exists() else ""


def main() -> None:
    print("pr-build sizes the lookup from the toolchain, not from either pin")
    m = re.search(
        r"LAKE_CACHE_MAX_REVS: \$\{\{ env\.TOOLCHAIN_CHANGED == '1' && '(\d+)' \|\| '(\d+)' \}\}",
        PR_BUILD)
    check(m is not None, "the limit is chosen by TOOLCHAIN_CHANGED")
    if m:
        check(
            m.group(1) == "1",
            "a toolchain move asks about HEAD alone (1), so a merge-group re-run can "
            "still meet its own published outputs",
        )
        check(
            int(m.group(2)) > 1,
            f"every other candidate keeps a walk (got {m.group(2)})",
        )
    check(
        re.search(r'if \[ "\$f" = "lean-toolchain" \]; then toolchain_changed=1; fi', PR_BUILD)
        is not None,
        "only lean-toolchain sets the signal (a manifest bump keeps its ancestors)",
    )
    check(
        'echo "TOOLCHAIN_CHANGED=1" >> "$GITHUB_ENV"' in PR_BUILD,
        "the scope guard exports TOOLCHAIN_CHANGED",
    )
    # The export sits inside `if [ "$toolchain_changed" = "1" ]`, which is only reachable
    # after both tree entries were read; an unreadable one `continue`s past it.
    check(
        re.search(
            r'if \[ -z "\$mb_entry" \] \|\| \[ -z "\$head_entry" \]; then\n'
            r'\s+pins_known=0\n[^\n]*\n\s+continue',
            PR_BUILD) is not None,
        "an unreadable tree entry skips the comparison, so the signal stays unset",
    )

    print("the script forwards the caller's limit to Lake")
    for want in ("1", "1000"):
        argv = lake_argv(want)
        check(
            re.search(rf"--max-revs={want}(?!\d)", argv) is not None,
            f"asks Lake for {want} revision(s) when told {want}",
        )

    if failures:
        print(f"\n{len(failures)} check(s) failed")
        sys.exit(1)
    print("\nlake cache lookup sizing checks passed")


if __name__ == "__main__":
    main()
