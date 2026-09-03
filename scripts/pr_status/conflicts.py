#!/usr/bin/env python3
"""Label a PR that has stopped merging into its base branch, and say so once.

A PR becomes conflicted because the BASE moved, not because its author did
anything, which makes it the one transition nothing else here can see. Every other
trigger in this repository is scoped to the PR -- `pull_request_target`, a
`pr-build` / `Review` `workflow_run`, an `issue_comment` -- and the base moving
fires none of them. So a PR could pick up a conflict and nothing anywhere said so:
`stuck_alerts.py` deliberately skips a conflicting PR (it is not being wrongly
withheld by the merge path) and `housekeeping.py` only retires PRs that are
blocking under review, so a conflicted-but-approved PR was reaped by nothing
either. It rotted silently.

The `merge-conflict` label is deliberately NOT part of the mutually-exclusive set
`labels.py` maintains, and nothing else reads or writes it. Conflict is orthogonal
to where a PR sits in the pipeline: a PR can be awaiting review AND conflicting,
and saying both is more useful than having one hide the other. Keeping them apart
also means conflict state never enters `core.derive` and can never lose a
precedence argument against CI or review state.

THE LABEL IS THE STATE. Whether an episode is open is just "is the label on the
PR", so there is no marker to parse and no way to fail to recognise our own
bookkeeping; a wrong label self-heals on the next run. It also makes the problem
measurable without anything extra, because GitHub timestamps label changes:
`labeled merge-conflict` -> `unlabeled merge-conflict` in the PR timeline is the
observed episode, recorded by GitHub rather than self-reported.

Two ordering decisions carry the weight, and both are deliberate:

  * **The comment is posted BEFORE the label.** The label is what suppresses a
    repeat, so adding it first means a comment that then fails is never retried --
    the notice is lost silently, which is the one failure this module cannot have.
    Commenting first fails the other way: a label write that fails after a
    successful comment costs a duplicate comment next run. A duplicate is
    annoying; a lost notification defeats the purpose.
  * **UNKNOWN is skipped per PR, never per run.** GitHub computes `mergeable`
    lazily, so a read taken just after the base moved answers UNKNOWN and only
    schedules the merge. Those PRs are re-read a few times; any that stay unknown
    are LEFT EXACTLY AS THEY ARE -- not labelled, not cleared -- while every PR
    whose state we do know is still processed. A PR whose head has diverged from
    its branch tip can sit at `mergeable: null` indefinitely (that is what
    `stuck_alerts.py`'s `diverged-head` detector is for), and one such PR must not
    be able to stop the others being labelled.

A PR carrying a hold label is left entirely alone, not labelled-but-silent. The
label means "the author has been told", and labelling without commenting would
break that: once the hold came off, the label would already claim the conflict was
handled and it would stay silent for good.

Only OPEN PRs are read, so a PR closed while labelled keeps the label. That is
accurate -- it was conflicting when it closed -- but it means a timeline has no
closing event for that episode, which anyone measuring should allow for.

Usage:
    conflicts.py sweep [--dry-run]

Environment:
    GH_REPO                   default "TauCetiProject/TauCeti"
    GH_TOKEN / GITHUB_TOKEN   used by `gh` (needs issues:write)

Only python3's standard library and an authenticated `gh` CLI are required.
"""

import json
import subprocess
import sys
import time

import core

REPO = core.REPO
LABEL = "merge-conflict"
LABEL_COLOR = "b60205"
LABEL_DESCRIPTION = "No longer merges cleanly into its base branch; needs a rebase"

# How many times to re-read the PRs GitHub answered UNKNOWN for, and how long to
# wait between rounds. The first read is what SCHEDULES the merge, so there is
# always at least one re-read; the busiest moment is just after a push to the base,
# when every open PR needs recomputing at once.
UNKNOWN_ROUNDS = 4
UNKNOWN_WAIT_SECONDS = 10.0

# Mirrors stuck_alerts.HOLD_LABELS: a PR carrying one of these is parked on purpose.
HOLD_LABELS = {"keep", "hold", "wip", "human", "do-not-close", "blocked"}

COMMENT = """\
⚠️ This PR no longer merges into `{base}`. Rebase it onto current `{base}` \
(or merge `{base}` into it) and push — nothing downstream can make progress until \
then, since a green build and an approving review on this head still cannot merge.

Do check what the conflict actually is before resolving it mechanically. If \
`{base}` has since landed its own version of something this PR adds, part of it \
may be superseded, and the right answer is to drop that part — or close the PR — \
rather than to reconcile the text. That is an authoring decision."""

OPEN_PRS_QUERY = """
query($owner:String!, $name:String!, $cursor:String) {
  repository(owner:$owner, name:$name) {
    pullRequests(states:OPEN, first:100, after:$cursor,
                 orderBy:{field:CREATED_AT, direction:ASC}) {
      pageInfo { hasNextPage endCursor }
      nodes {
        number mergeable baseRefName
        labels(first:100) { nodes { name } }
      }
    }
  }
}
"""


def log(message):
    print(message, flush=True)


def _gh(args):
    result = subprocess.run(["gh", *args], capture_output=True, text=True)
    if result.returncode != 0:
        # Summarise the command rather than echoing it: a failing comment would
        # otherwise reprint the whole comment body into the log, once per PR.
        shown = " ".join(a.split("=", 1)[0] if a.startswith("-f") or "=" in a else a
                         for a in args)
        raise RuntimeError(f"gh {shown} failed: {result.stderr.strip()}")
    return result.stdout


def open_prs():
    """Every open PR as {number, conflicting, base, labels}, in one query per 100.

    `conflicting` is GitHub's CONFLICTING / MERGEABLE / UNKNOWN normalised to
    True / False / None. None means "not computed", never "no conflict".
    """
    owner, _, name = REPO.partition("/")
    rows, cursor = [], None
    while True:
        args = ["api", "graphql", "-f", f"query={OPEN_PRS_QUERY}",
                "-f", f"owner={owner}", "-f", f"name={name}"]
        if cursor:
            args += ["-f", f"cursor={cursor}"]
        page = json.loads(_gh(args))
        if page.get("errors"):
            raise RuntimeError(f"GitHub GraphQL errors: {page['errors']}")
        block = page["data"]["repository"]["pullRequests"]
        for node in block["nodes"]:
            rows.append({
                "number": node["number"],
                "conflicting": {"CONFLICTING": True, "MERGEABLE": False}.get(
                    node.get("mergeable")),
                "base": node.get("baseRefName") or "the base branch",
                "labels": [l["name"] for l in (node.get("labels") or {}).get("nodes", [])],
            })
            # The nested connection is not paginated. 100 is far past anything this
            # repo uses, but a PR that hit the cap could hide our own label from us
            # and be commented on twice, so say so rather than fail silently.
            if len(rows[-1]["labels"]) >= 100:
                log(f"PR #{rows[-1]['number']} reports 100 labels; the list may be "
                    f"truncated and its {LABEL} state unreliable")
        if not block["pageInfo"]["hasNextPage"]:
            return rows
        cursor = block["pageInfo"]["endCursor"]


def resolve_unknowns(prs, sleep=time.sleep):
    """Re-read the PRs GitHub answered UNKNOWN for, in place.

    Whatever is still unknown afterwards keeps `conflicting = None`, and the caller
    leaves those PRs alone. Crucially this never abandons the run: a PR that is
    permanently unknown costs itself, not everyone after it.
    """
    for _ in range(UNKNOWN_ROUNDS - 1):
        pending = {pr["number"] for pr in prs if pr["conflicting"] is None}
        if not pending:
            return
        log(f"{len(pending)} PR(s) with mergeability not yet computed; re-reading")
        sleep(UNKNOWN_WAIT_SECONDS)
        try:
            fresh = {row["number"]: row for row in open_prs()}
        except Exception as exc:
            # Giving up here would abandon every PR we DO know about, which is the
            # same run-wide failure this module exists to avoid.
            log(f"re-read failed ({exc}); continuing with what is already known")
            return
        for index, pr in enumerate(prs):
            row = fresh.get(pr["number"])
            # Replace the whole row: the PR may have gained a label or changed base
            # while we waited, and pairing fresh mergeability with stale labels is
            # how a PR gets commented on twice.
            if pr["conflicting"] is None and row and row["conflicting"] is not None:
                prs[index] = row
    still = sorted(pr["number"] for pr in prs if pr["conflicting"] is None)
    if still:
        log(f"mergeability still unknown for {still}; leaving them exactly as they are")


def ensure_label():
    """Make sure the label exists, or RAISE. Self-provisioning like labels.py.

    Raising matters more than it looks. The label is the episode state, so if it
    is missing every comment still goes out and every label write then fails,
    leaving no state behind -- and the next run comments the same PRs again. On a
    queue with sixteen conflicts that is sixteen duplicate comments per run. So an
    ambiguous probe is never read as "it is there": we try to create it anyway
    (creation is idempotent) and give up loudly if we still cannot confirm it,
    which stops the sweep before it comments on anything.
    """
    probe = subprocess.run(["gh", "api", f"/repos/{REPO}/labels/{LABEL}"],
                           capture_output=True, text=True)
    if probe.returncode == 0:
        return
    create = subprocess.run(
        ["gh", "api", "--method", "POST", f"/repos/{REPO}/labels",
         "-f", f"name={LABEL}", "-f", f"color={LABEL_COLOR}",
         "-f", f"description={LABEL_DESCRIPTION}"], capture_output=True, text=True)
    if create.returncode == 0:
        log(f"created the {LABEL} label")
        return
    if "already_exists" in create.stderr:
        return
    raise RuntimeError(
        f"cannot confirm the {LABEL} label exists, so not commenting on anything: "
        f"probe said {probe.stderr.strip()!r}; create said {create.stderr.strip()!r}")


def reconcile(pr, dry_run=False):
    """Bring one PR's label into line with its mergeability.

    Returns "labelled", "cleared", "unchanged", "parked", or "skipped"
    (mergeability unknown).
    """
    number, labelled = pr["number"], LABEL in pr["labels"]
    if pr["conflicting"] is None:
        return "skipped"
    if pr["conflicting"] == labelled:
        return "unchanged"
    if not pr["conflicting"]:
        log(f"PR #{number}: merges again; removing {LABEL}")
        if not dry_run:
            _gh(["api", "--method", "DELETE",
                 f"/repos/{REPO}/issues/{number}/labels/{LABEL}"])
        return "cleared"

    if HOLD_LABELS.intersection(name.lower() for name in pr["labels"]):
        # Left entirely alone, not labelled-but-silent. The label means "we have
        # told the author"; labelling without commenting would break that, and the
        # conflict would then stay silent forever once the hold came off, because
        # the label already says it was handled.
        log(f"PR #{number}: conflicts with {pr['base']}, but is parked; leaving it")
        return "parked"
    log(f"PR #{number}: conflicts with {pr['base']}")
    if not dry_run:
        # Comment BEFORE labelling: the label is what suppresses a repeat, so a
        # comment that fails after it would never be retried. See the module docs.
        _gh(["api", "--method", "POST", f"/repos/{REPO}/issues/{number}/comments",
             "-f", f"body={COMMENT.format(base=pr['base'])}"])
        _gh(["api", "--method", "POST", f"/repos/{REPO}/issues/{number}/labels",
             "-f", f"labels[]={LABEL}"])
    return "labelled"


def sweep(dry_run=False, sleep=time.sleep):
    """Reconcile every open PR. Returns the number of failures."""
    prs = open_prs()
    resolve_unknowns(prs, sleep=sleep)
    known = [pr for pr in prs if pr["conflicting"] is not None]
    log(f"{len(prs)} open PR(s); {sum(1 for p in known if p['conflicting'])} conflicting, "
        f"{len(prs) - len(known)} not computable this run")
    if not dry_run and any(p["conflicting"] for p in known):
        ensure_label()

    failures = 0
    for pr in known:
        try:
            reconcile(pr, dry_run=dry_run)
        except Exception as exc:
            # One PR failing must not cost the rest their label, which is exactly
            # the starvation this module exists to avoid.
            log(f"PR #{pr['number']}: {exc}")
            failures += 1
    return failures


def main(argv):
    if len(argv) < 2 or argv[1] != "sweep":
        print(__doc__)
        return 2
    failures = sweep(dry_run="--dry-run" in argv[2:])
    if failures:
        log(f"conflict sweep: {failures} PR(s) failed")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
