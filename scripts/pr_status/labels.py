#!/usr/bin/env python3
"""Keep exactly one status label on every open TauCeti PR.

The five labels are mutually exclusive; together they say, at a glance in the PR
list, where a PR is in the pipeline:

    awaiting-CI         CI has not yet reported on the latest commit
    awaiting-review     CI is green; waiting for review verdicts
    review-in-progress  a review is running on this exact commit right now
    awaiting-author     the build failed or a review requested changes
    ready-to-merge      CI green and every rubric approved

All five are derived here from the PR's status (core.derive) and this sink is the
SOLE writer of them, so the "exactly one" invariant is CI's alone to keep -- it
never depends on any worker or review harness behaving a particular way. reconcile
is idempotent and convergent: it reads GitHub truth afresh and drives the label
set to the single correct value.

`review-in-progress` is derived from the review engine's in-flight marker
(core.inprogress_from), treated as an optional, documented signal that any review
harness MAY post: a live (unexpired, head-exact) marker while the PR is otherwise
`awaiting-review` shows `review-in-progress`. A harness that posts no marker simply
leaves the PR at `awaiting-review` during review -- graceful, never wrong -- and
the marker's TTL means a crashed review self-heals (the hourly sweep clears it even
with no other event). A terminal PR (merged/closed) carries no status label.

Usage:
    labels.py reconcile <pr_number> [--ci STATE]

`--ci STATE` (running|success|failure|none) forces the CI state instead of reading
the `build` commit status; used only by the backfill/tests.

Environment:
    GH_REPO                   default "TauCetiProject/TauCeti"
    GH_TOKEN / GITHUB_TOKEN   used by `gh` for the GitHub API (needs issues:write)

Only python3's standard library and an authenticated `gh` CLI are required.
"""

import subprocess
import sys

import core

REPO = core.REPO

# label -> (hex color, description). Created on first use, like the roadmap labels, so setting this
# up needs no manual label creation.
LABELS = {
    "awaiting-CI":        ("fbca04", "CI has not yet reported on the latest commit"),
    "awaiting-review":    ("1d76db", "CI is green; waiting for review verdicts"),
    "review-in-progress": ("a371f7", "A review is running on this exact commit right now"),
    "awaiting-author":    ("d93f0b", "The build failed or a review requested changes; author action needed"),
    "ready-to-merge":     ("0e8a16", "CI green and every rubric approved; ready to merge"),
}
STATUS_LABELS = list(LABELS)


def log(msg):
    print(msg, flush=True)


def derived_label(status):
    """The one status label for `status`, or None if the PR is terminal (merged/closed).

    Precedence:
        PR merged/closed                       -> None (no status label)
        CI not reported yet / running          -> awaiting-CI
        CI failed                              -> awaiting-author
        CI green, review requested changes     -> awaiting-author
        CI green, every rubric approved        -> ready-to-merge
        CI green, review pending + live marker -> review-in-progress
        CI green, review pending, no marker    -> awaiting-review
    """
    if status["lifecycle"] != "open":
        return None
    ci = status["ci"]
    if ci in (None, "running"):
        return "awaiting-CI"
    if ci == "failure":
        return "awaiting-author"
    # ci == "success"
    review = status["review"]
    if review == "changes":
        return "awaiting-author"
    if review == "approved":
        return "ready-to-merge"
    # review pending ("none" or "running"): a live in-flight marker upgrades to review-in-progress.
    if status.get("review_inprogress"):
        return "review-in-progress"
    return "awaiting-review"


# ----- GitHub label writes (via gh; core.gh_api handles reads) ----------------

def _run(args):
    return subprocess.run(["gh", "api", *args], capture_output=True, text=True)


def current_status_labels(pr):
    """The status labels currently on the PR (a subset of STATUS_LABELS)."""
    names = core.gh_api(
        f"/repos/{REPO}/issues/{pr}/labels",
        jq=".[].name", paginate=True,
    ).splitlines()
    return [n for n in names if n in STATUS_LABELS]


def ensure_label(name):
    """Create the label if it does not exist yet (idempotent). Only a clear 404 on the probe means
    'absent, create it'; any other probe failure is left alone (the add may still succeed, and we do
    not want to mask a token/permission error as a missing label)."""
    probe = _run([f"/repos/{REPO}/labels/{name}"])
    if probe.returncode == 0:
        return
    if "404" not in probe.stderr:
        return
    color, description = LABELS[name]
    create = _run([
        "--method", "POST", f"/repos/{REPO}/labels",
        "-f", f"name={name}", "-f", f"color={color}", "-f", f"description={description}",
    ])
    # A concurrent create (422 already_exists) is fine; anything else is a real error.
    if create.returncode != 0 and "already_exists" not in create.stderr:
        raise RuntimeError(f"gh api create label {name} failed: {create.stderr.strip()}")


def add_label(pr, name):
    ensure_label(name)
    r = _run(["--method", "POST", f"/repos/{REPO}/issues/{pr}/labels", "-f", f"labels[]={name}"])
    if r.returncode != 0:
        raise RuntimeError(f"gh api add label {name} failed: {r.stderr.strip()}")
    log(f"added {name}")


def remove_label(pr, name):
    r = _run(["--method", "DELETE", f"/repos/{REPO}/issues/{pr}/labels/{name}"])
    # A label already gone (the label is not on the issue) is the end state we want. GitHub answers a
    # DELETE of an unattached label with 404 "Label does not exist"; tolerate exactly that.
    if r.returncode != 0 and not ("404" in r.stderr and "does not exist" in r.stderr):
        raise RuntimeError(f"gh api remove label {name} failed: {r.stderr.strip()}")
    log(f"removed {name}")


def reconcile(pr, ci_override=None):
    status = core.derive(pr, ci_override)
    desired = derived_label(status)          # one of STATUS_LABELS, or None (terminal)
    current = set(current_status_labels(pr))

    for name in current:
        if name != desired:
            remove_label(pr, name)
    if desired is not None and desired not in current:
        add_label(pr, desired)

    log(f"PR #{pr}: lifecycle={status['lifecycle']} ci={status['ci']} review={status['review']} "
        f"inprogress={status['review_inprogress']} -> label={desired or '(none)'}")


def main(argv):
    if len(argv) < 3 or argv[1] != "reconcile":
        print(__doc__)
        return 2
    pr = argv[2].lstrip("#")
    if not pr.isdigit():
        log(f"not a PR number: {argv[2]!r}")
        return 0
    rest = argv[3:]
    ci_override = None
    if "--ci" in rest:
        ci_override = rest[rest.index("--ci") + 1]
    reconcile(pr, ci_override)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
