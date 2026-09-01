#!/usr/bin/env python3
"""Regression checks for exact-commit PR performance profiling."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "pr-profile.yml"


def require(text: str, fragment: str) -> None:
    assert fragment in text, f"pr-profile.yml must contain {fragment!r}"


def forbid(text: str, fragment: str) -> None:
    assert fragment not in text, f"pr-profile.yml must not contain {fragment!r}"


def main() -> None:
    text = WORKFLOW.read_text()

    # Both sides of the comparison are immutable Git commits. Ordinary PRs use
    # their merge base; merge groups use the queue's immutable base commit.
    require(text, "echo \"comparison_base=$COMPARISON_BASE\"")
    require(text, "ref: ${{ steps.pr.outputs.comparison_base }}")
    require(text, "ref: ${{ steps.pr.outputs.sha }}")
    require(text, "path: base")
    require(text, "path: head")
    require(text, "fetch-depth: 0")

    # Lake configuration is attested before Lake can execute, and forward pin
    # bumps stay autonomous while incomparable cross-toolchain ratios are skipped.
    require(text, "gate/scripts/attest-pr-config.sh")
    require(text, "gate/scripts/check-bump.sh policy base head")
    require(text, "validated pin/toolchain bump; cost ratio intentionally skipped")

    # Cache lookup walks all fetched ancestry, and executable profiling helpers
    # come from the workflow-pinned trusted checkout rather than the PR.
    require(text, 'LAKE_CACHE_MAX_REVS: "0"')
    require(text, "../gate/scripts/profile/measure.sh")

    # Do not regress to constructing a synthetic source/configuration overlay.
    for fragment in (
        "git merge --no-commit",
        "path: pr",
        "cp -a pr/TauCeti",
        "cp -a pr/TauCeti.lean",
        "head/scripts/profile/measure.sh",
    ):
        forbid(text, fragment)

    print("pr-profile exact-commit workflow checks passed")


if __name__ == "__main__":
    main()
