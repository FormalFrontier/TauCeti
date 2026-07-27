#!/usr/bin/env python3
"""Queue housekeeping: retire PRs that are spent or stuck, and close duplicate roadmap PRs.

Green PRs merge on their own (the merge queue, fed by auto-merge.yml). This covers the janitorial
jobs, in CI so the autonomous worker can stay focused on producing work, and so that EVERY PR ends up
either merged or closed — never stranded:

  empty    Close a roadmap PR (one carrying the `<!--tauceti-target:v1 ...-->` marker) whose diff
           against main is empty — its changes already landed in main, typically because a sibling
           worker attempt at the same target merged first. dedup only matches an OPEN twin, so once the
           twin merges this is what reaps the loser, instead of leaving it for the 7-day stale timer.
           Acts only on a PR quiet for EMPTY_QUIET_MINUTES, so an actively-pushing worker is never raced.
  budget   Close a PR that has been reviewed to the round cap (REVIEW_BUDGET) at its current head and
           is still blocking. CI is the single budget authority — the worker no longer caps itself — so
           a PR is reviewed and fixed until it merges or this closes it. The decision is read from the
           scoreboard ledger (`full_rounds` + per-rubric `states`), so it holds whether or not the
           worker is running. A manual `review-budget-spent` label force-closes a PR early.
  dedup    Close a newer PR that authors the same roadmap target (the `<!--tauceti-target:v1 ...-->`
           body marker) as an older open one. Keep the lowest PR number.
  stale    Close a PR whose latest review scoreboard still has a blocking rubric and which has had no
           activity for STALE_DAYS (default 7): a request for changes nobody acted on, under budget.

The one override is a `keep` label (also `hold`/`wip`/`human`/`do-not-close`): a PR with one of those
is never auto-closed. By design these jobs do NOT spare human-touched PRs — anyone who wants a PR held
adds `keep`. A failed close makes the job exit nonzero.

A scoreboard is trusted only if it carries the `tauceti-scoreboard` marker AND its author is
repo-associated (OWNER/MEMBER/COLLABORATOR) — the same trust the worker applies. The reviewer and the
PR author are frequently the same account (the worker reviews its own roadmap PRs), so trust is by
association, not by "not the author": an external author cannot forge a repo-associated comment.

Env: GH_TOKEN (a token that can close PRs), REPO (owner/name), optional DRY_RUN=1, REVIEW_BUDGET,
BUDGET_LABEL, STALE_DAYS, EMPTY_QUIET_MINUTES.
"""
import datetime
import json
import os
import re
import subprocess
import sys

REPO = os.environ["REPO"]

# The trusted-scoreboard parse lives once, in the pr_status package; import it rather than keeping a
# second copy here (the two had drifted on the meta regex). This script is parameterised by $REPO, so
# point core's reads at the same repo.
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "pr_status"))
import core  # noqa: E402

core.REPO = REPO

DRY_RUN = os.environ.get("DRY_RUN") == "1"
# Lifetime review rounds a PR may accumulate without going all-green before CI retires it. CI is the
# single budget authority: the worker no longer caps itself, so a PR is reviewed/fixed until it merges
# or this cap closes it. Read from the scoreboard ledger's `full_rounds`.
REVIEW_BUDGET = int(os.environ.get("REVIEW_BUDGET", "10"))
# Optional manual force-abandon label (a human may add it to retire a PR early). The automatic budget
# decision is computed from the ledger, not from this label.
BUDGET_LABEL = os.environ.get("BUDGET_LABEL", "review-budget-spent")
# How long a blocked PR may sit untouched (under budget) before the stale job retires it.
STALE_DAYS = int(os.environ.get("STALE_DAYS", "7"))
# How long an empty-diff roadmap PR must be QUIET before the empty job closes it — long enough that an
# actively-pushing worker (which would bump updatedAt) is never raced into a wrong close.
EMPTY_QUIET_MINUTES = int(os.environ.get("EMPTY_QUIET_MINUTES", "30"))

TARGET_MARKER_RE = re.compile(r"<!--tauceti-target:v1 \{[^}]*\}-->")
TARGET_ID_RE = re.compile(r'"id"\s*:\s*"([^"]+)"')
# The reviewer posts one scoreboard comment per PR carrying a machine-readable meta block: `full_rounds`
# (lifetime review passes) and `states` (per-rubric verdict). A rubric `state` not in {green, stale} is
# blocking ("stale" is a prior approval carried forward, not a block).
NONBLOCKING_STATES = {"green", "stale"}
KEEP_LABELS = {"keep", "hold", "wip", "human", "do-not-close"}
BUDGET_COMMENT = (
    "Closing automatically: this PR was reviewed to the round cap without reaching an all-green review, "
    "so the queue housekeeping is retiring it to keep things moving. The branch is kept, so nothing is "
    "lost. It is completely fine to open a fresh PR once you have had another think about the approach. "
    "Add the `keep` label if you would rather it stay open.")
DEDUP_COMMENT = (
    "Closing automatically: this PR authors the same roadmap target (`{tid}`) as the older open #{kept}. "
    "The queue housekeeping keeps the earlier PR and closes this duplicate to avoid redundant review. "
    "The branch is kept; add the `keep` label if it is intentionally distinct.")
STALE_COMMENT = (
    "Closing automatically: this PR's last review still asks for changes (blocking: {blocking}) and it "
    "has sat untouched for over {days} days, so the queue housekeeping is retiring it to keep things "
    "moving. The branch is kept, so nothing is lost. It is completely fine to open a fresh PR once the "
    "findings are addressed. Add the `keep` label if you would rather it stay open.")
EMPTY_COMMENT = (
    "Closing automatically: this PR's diff against `main` is empty — all of its changes are already in "
    "`main` (typically a sibling attempt at the same roadmap target merged first), so there is nothing "
    "left to merge. The branch is kept, so nothing is lost. Add the `keep` label if you want it to stay "
    "open.")


def gh_json(args):
    r = subprocess.run(["gh", *args], capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args)} failed: {r.stderr.strip()}")
    return json.loads(r.stdout or "null")


def has_keep_label(pr: dict) -> bool:
    return bool({(l.get("name") or "").lower() for l in (pr.get("labels") or [])} & KEEP_LABELS)


def has_label(pr: dict, name: str) -> bool:
    return name.lower() in {(l.get("name") or "").lower() for l in (pr.get("labels") or [])}


def keep_label_live(pr: int) -> bool:
    """Re-check the keep label right before closing: a human may have added it since the list."""
    live = gh_json(["pr", "view", str(pr), "--repo", REPO, "--json", "labels"]) or {}
    return has_keep_label(live)


def parse_ts(s: str) -> datetime.datetime:
    """Parse a GitHub ISO-8601 timestamp (trailing 'Z') into an aware datetime."""
    return datetime.datetime.fromisoformat((s or "").replace("Z", "+00:00"))


def latest_scoreboard_meta(pr: int):
    """The meta block of the newest TRUSTED review scoreboard comment, or None. Trust = the
    `tauceti-scoreboard` marker AND a repo-associated author (so an external author cannot forge a
    verdict). Delegates to the shared `core.scoreboard_meta` so that parse lives in one place; fails
    safe (None) on any API/parse error, so a hiccup never causes a wrong close."""
    try:
        return core.scoreboard_meta(pr) or None
    except Exception as e:
        print(f"#{pr}: scoreboard fetch failed ({e}); leaving it", file=sys.stderr)
        return None


def blocking_rubrics(meta: dict) -> list:
    """The rubrics whose state is blocking (not green or stale) in the scoreboard ledger."""
    return sorted(k for k, v in (meta.get("states") or {}).items() if v not in NONBLOCKING_STATES)


def close(pr: int, comment: str) -> bool:
    """Close the PR with a comment. Returns True on success (or in dry-run), False on failure."""
    if DRY_RUN:
        print(f"[dry-run] would close #{pr}: {comment[:60]}...")
        return True
    r = subprocess.run(["gh", "pr", "close", str(pr), "--repo", REPO, "--comment", comment],
                       capture_output=True, text=True)
    if r.returncode == 0:
        print(f"closed #{pr}")
        return True
    print(f"close of #{pr} failed: {r.stderr.strip()}", file=sys.stderr)
    return False


def main() -> int:
    failures = 0
    suffix = " [dry-run]" if DRY_RUN else ""

    # empty: a PR whose diff against main is empty has nothing left to merge — its changes are already in
    # main (typically a sibling worker attempt at the same roadmap target merged first). dedup only
    # matches an OPEN twin, so once the twin merges nothing reaps the loser; this closes it directly
    # instead of waiting out the 7-day stale timer (and stops the worker thrashing on a done target).
    # Two guards keep a destructive close safe: it is scoped to autonomous roadmap PRs (those carrying the
    # tauceti-target marker), so an intentionally empty human PR is left alone; and it acts only on a PR
    # QUIET for EMPTY_QUIET_MINUTES, so an actively-pushing worker (which bumps updatedAt) is never raced.
    # The quiet window is also what guarantees the diff stats are settled: GitHub recomputes
    # changedFiles/additions/deletions promptly on each push or base move, so a PR untouched for the whole
    # window has accurate, stable stats. (The `mergeable` field is NOT a usable signal here — it is
    # computed lazily and a cold query returns UNKNOWN even for a long-settled PR, which would make the
    # close flaky.) Emptiness, draft, keep, and quiet are all re-confirmed from a fresh per-PR view right
    # before the close, so a just-pushed PR (now active, or a now-non-empty diff) is never closed.
    quiet_cutoff = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(minutes=EMPTY_QUIET_MINUTES)
    open_empty = gh_json(["pr", "list", "--repo", REPO, "--state", "open", "--limit", "1000",
                          "--json", "number,isDraft,labels,body,updatedAt"]) or []
    cand = [p for p in open_empty if p.get("isDraft") is False and not has_keep_label(p)
            and TARGET_MARKER_RE.search((p.get("body") or "").replace("\n", " "))
            and parse_ts(p.get("updatedAt", "")) < quiet_cutoff]
    print(f"empty: {len(cand)} quiet roadmap PR(s) to check for an empty diff{suffix}")
    for p in cand:
        n = p["number"]
        v = gh_json(["pr", "view", str(n), "--repo", REPO,
                     "--json", "isDraft,changedFiles,additions,deletions,labels,updatedAt"]) or {}
        # Final eligibility read right before the close: skip on ANY change since the listing — a pushed
        # commit or new activity (updatedAt back inside the quiet window), or a new draft/keep state.
        if (v.get("isDraft") is not False or has_keep_label(v)
                or parse_ts(v.get("updatedAt", "")) >= quiet_cutoff):
            continue
        # A PR quiet for the whole window has settled diff stats; an empty diff here is genuinely empty.
        if v.get("changedFiles") != 0 or v.get("additions") != 0 or v.get("deletions") != 0:
            continue
        print(f"empty: #{n} (empty diff, quiet >{EMPTY_QUIET_MINUTES}m — content already in main)")
        failures += not close(n, EMPTY_COMMENT)

    # budget: a PR reviewed to REVIEW_BUDGET rounds at its CURRENT head and still blocking is terminal —
    # close it. Read from the scoreboard ledger (full_rounds + states), so it holds even when the worker
    # is idle. Requiring the scoreboard to be AT the current head means a just-pushed fix that has not
    # been re-reviewed yet is never closed — it gets its re-review first; only a head reviewed to the cap
    # and still blocking is spent. A manual `review-budget-spent` label force-closes regardless.
    open_full = gh_json(["pr", "list", "--repo", REPO, "--state", "open", "--limit", "1000",
                         "--json", "number,isDraft,headRefOid,labels"]) or []
    cand = [p for p in open_full if p.get("isDraft") is False and not has_keep_label(p)]
    print(f"budget: scanning {len(cand)} open PR(s) (cap {REVIEW_BUDGET} rounds){suffix}")
    for p in cand:
        n, head = p["number"], p.get("headRefOid", "")
        if has_label(p, BUDGET_LABEL):
            reason = f"manual {BUDGET_LABEL} label"
        else:
            meta = latest_scoreboard_meta(n)
            if not meta or (meta.get("head_sha") or "") != head:
                continue                       # no trusted scoreboard, or it is stale (head moved) — wait
            fr, blk = meta.get("full_rounds"), blocking_rubrics(meta)
            if not (isinstance(fr, int) and fr >= REVIEW_BUDGET and blk):
                continue
            reason = f"{fr} rounds at head, still blocking {', '.join(blk)}"
        if keep_label_live(n):
            print(f"budget: #{n} reached the cap but has a keep label; leaving it")
            continue
        print(f"budget: #{n} ({reason})")
        failures += not close(n, BUDGET_COMMENT)

    # dedup: a newer PR sharing a tauceti-target id with an older open one (keep the lowest number).
    # List-only (the marker is in the body), so this pages cheaply; the marker is on roadmap PRs only.
    limit = 2000
    prs = gh_json(["pr", "list", "--repo", REPO, "--state", "open", "--limit", str(limit),
                   "--json", "number,isDraft,body,labels"]) or []
    if len(prs) >= limit:
        print(f"warning: hit the {limit}-PR list limit; some open PRs may not be de-duplicated",
              file=sys.stderr)
    prs = [p for p in prs if not p.get("isDraft")]
    print(f"dedup: scanning {len(prs)} open PR(s){suffix}")
    seen: dict = {}
    for p in sorted(prs, key=lambda x: x["number"]):
        body = (p.get("body") or "").replace("\n", " ")
        mk = TARGET_MARKER_RE.search(body)
        if not mk:
            continue
        mid = TARGET_ID_RE.search(mk.group(0))
        if not mid:
            continue
        tid = mid.group(1)
        if tid not in seen:
            seen[tid] = p["number"]
            continue
        if has_keep_label(p):
            print(f"dedup: #{p['number']} duplicates #{seen[tid]} (target '{tid}') but has a keep "
                  "label; leaving it")
            continue
        print(f"dedup: #{p['number']} duplicates #{seen[tid]} (target '{tid}')")
        failures += not close(p["number"], DEDUP_COMMENT.format(tid=tid, kept=seen[tid]))

    # stale: a PR with a blocking rubric (under budget — the budget job takes the spent ones) that has
    # had no activity for STALE_DAYS. updatedAt bumps on any push/comment/label, so a still-worked PR is
    # never stale; this catches a blocked PR everyone has walked away from.
    cutoff = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=STALE_DAYS)
    open_prs = gh_json(["pr", "list", "--repo", REPO, "--state", "open", "--limit", "1000",
                        "--json", "number,isDraft,labels,updatedAt"]) or []
    # isDraft must be explicitly False (fail closed: an unknown draft state is never stale-closed).
    fresh = [p for p in open_prs if p.get("isDraft") is False and not has_keep_label(p)
             and parse_ts(p.get("updatedAt", "")) < cutoff]
    print(f"stale: {len(fresh)} open PR(s) untouched for >{STALE_DAYS}d to check{suffix}")
    for p in fresh:
        meta = latest_scoreboard_meta(p["number"])
        if not meta:
            continue
        blk = blocking_rubrics(meta)
        if not blk:
            continue
        if keep_label_live(p["number"]):
            print(f"stale: #{p['number']} gained a keep label since listing; leaving it")
            continue
        print(f"stale: #{p['number']} (blocking {', '.join(blk)}, untouched >{STALE_DAYS}d)")
        failures += not close(p["number"], STALE_COMMENT.format(blocking=", ".join(blk), days=STALE_DAYS))

    if failures:
        print(f"housekeeping: {failures} close(s) failed", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except RuntimeError as e:
        print(f"housekeeping: {e}", file=sys.stderr)
        sys.exit(1)
