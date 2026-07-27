#!/usr/bin/env python3
"""Shared derivation of a TauCeti PR's status from GitHub truth.

This is the single place that reads what a PR's status *is* -- its lifecycle
(open / merged / closed), its `build` CI state, and its review state (from the
canonical `<!--tauceti-scoreboard-->` comment's meta JSON), plus whether a review
is in flight right now (from the engine's `<!--tauceti-review-in-progress-->`
marker). Every status *sink* imports it and renders that one truth its own way:

  * zulip.py   -> two independent groups of emoji reactions on the PR's message
  * labels.py  -> exactly one of the five status labels on the PR itself

Keeping the derivation here means the two sinks can never disagree about what a
PR's state is: they read the same `derive()` and only differ in how they show it.

Everything here reads only trusted GitHub data. The two review signals -- the
scoreboard meta and the in-progress marker -- are taken only from comments by a
repo-associated author (OWNER/MEMBER/COLLABORATOR), so a fork PR author cannot
forge review state. Both are extracted from ONE comment fetch.

The module is a pure library -- importing it has no side effects, writes nothing,
and needs only python3's standard library plus an authenticated `gh` CLI (via
GH_TOKEN / GITHUB_TOKEN). It reads GitHub; it never touches Zulip or labels.
"""

import json
import os
import re
import subprocess
import time

REPO = os.environ.get("GH_REPO", "TauCetiProject/TauCeti")

SCOREBOARD_MARKER = "<!--tauceti-scoreboard-->"
# Greedy `\{.*\}` (with re.S) so a meta object with a nested `"states": {...}` is captured whole: a
# lazy `\{.*?\}` would stop at the first inner `}` and mis-parse it. `\s+`/`\s*` tolerate any spacing.
_META_RE = re.compile(r"<!--tauceti-meta:v1\s+(\{.*\})\s*-->", re.S)
# The engine's in-flight marker: `<!--tauceti-review-in-progress {json}-->`, carrying a `head` and an
# `expires_at` (epoch seconds) so a crashed reviewer self-clears. The format is owned by the review
# engine; we parse only those two fields (mirrors the worker's de-contention read).
_INPROGRESS_RE = re.compile(r"<!--tauceti-review-in-progress (.*?)-->", re.S)
_TRUSTED_ASSOC = ("OWNER", "MEMBER", "COLLABORATOR")


# ----- GitHub truth (via the gh CLI, authenticated by GH_TOKEN) ---------------

def gh_api(path, jq=None, paginate=False):
    cmd = ["gh", "api", path]
    if paginate:
        cmd.append("--paginate")
    if jq is not None:
        cmd += ["--jq", jq]
    out = subprocess.run(cmd, capture_output=True, text=True)
    if out.returncode != 0:
        raise RuntimeError(f"gh api {path} failed: {out.stderr.strip()}")
    return out.stdout


def pr_state(pr):
    """{'state','merged','head','title'} for the PR.

    Prefer the triggering event's payload, passed in via PR_STATE/PR_HEAD/
    PR_MERGED/PR_TITLE (a workflow that has the pull_request object can set these
    from github.event.pull_request, so a close/merge needs no GitHub API call at
    all). Fall back to the REST API when they aren't set (the workflow_run and
    issue_comment triggers, and the backfill), where the payload is absent or
    isn't the PR we're reconciling.
    """
    env_state = os.environ.get("PR_STATE")
    env_head = os.environ.get("PR_HEAD")
    if env_state and env_head:
        return {
            "state": env_state,
            "merged": os.environ.get("PR_MERGED") == "true",
            "head": env_head,
            "title": os.environ.get("PR_TITLE") or f"PR #{pr}",
        }
    d = json.loads(gh_api(f"/repos/{REPO}/pulls/{pr}"))
    return {
        "state": d["state"],                 # "open" | "closed"
        "merged": bool(d.get("merged")),
        "head": d["head"]["sha"],
        "title": d.get("title") or f"PR #{pr}",
    }


def trusted_comments(pr):
    """Issue comments authored by a repo-associated account (OWNER/MEMBER/COLLABORATOR), as
    `[{'body','updated'}]`. One paginated fetch, reused for both review signals below, so an
    untrusted fork-PR comment can never forge review state. The jq emits one compact object per
    line (valid JSONL across any number of pages)."""
    out = gh_api(
        f"/repos/{REPO}/issues/{pr}/comments?per_page=100",
        jq='.[] | select(.author_association|IN("OWNER","MEMBER","COLLABORATOR"))'
           ' | {body: .body, updated: .updated_at}',
        paginate=True,
    )
    rows = []
    for ln in out.splitlines():
        ln = ln.strip()
        if not ln:
            continue
        try:
            rows.append(json.loads(ln))
        except json.JSONDecodeError:
            pass
    return rows


def scoreboard_meta_from(comments):
    """The newest scoreboard comment's meta JSON ({} if none), from a trusted-comment list."""
    best = None
    for c in comments:
        if SCOREBOARD_MARKER in (c.get("body") or ""):
            if best is None or (c.get("updated") or "") >= (best.get("updated") or ""):
                best = c
    if best is None:
        return {}
    m = _META_RE.search(best.get("body") or "")
    if not m:
        return {}
    try:
        return json.loads(m.group(1))
    except json.JSONDecodeError:
        return {}


def scoreboard_meta(pr):
    """Convenience: the scoreboard meta for a PR (fetches trusted comments itself)."""
    return scoreboard_meta_from(trusted_comments(pr))


def inprogress_from(comments, head, now):
    """True iff some trusted comment carries an UNEXPIRED in-progress marker for exactly `head`.

    Head-exact (a new push is a new review unit, not covered by an old marker) and TTL-bounded
    (a crashed reviewer's marker self-clears once `expires_at` passes), mirroring the engine's own
    de-contention read. A malformed or non-matching marker is ignored."""
    for c in comments:
        for m in _INPROGRESS_RE.finditer(c.get("body") or ""):
            try:
                d = json.loads(m.group(1))
            except json.JSONDecodeError:
                continue
            exp = d.get("expires_at")
            if isinstance(exp, int) and exp > now and d.get("head") == head:
                return True
    return False


def newest_status(head, context):
    """(state, updated_at) of the newest commit status for `context`, else (None, None).

    per_page=100 so a burst of unrelated status events cannot push the wanted
    context (e.g. `build` / `bump-guard`) off the first page and hide it.
    """
    out = gh_api(
        f"/repos/{REPO}/commits/{head}/statuses?per_page=100",
        jq=f'[.[] | select(.context == "{context}")] | sort_by(.updated_at)'
           ' | last | {state: (.state // ""), updated_at: (.updated_at // "")}',
    ).strip()
    if not out:
        return None, None
    row = json.loads(out.splitlines()[0])
    if not row.get("state"):
        return None, None
    return row["state"], row.get("updated_at") or None


def ci_status(head):
    """'running' | 'success' | 'failure' | None from the `build` commit status."""
    state, _ = newest_status(head, "build")
    if state == "pending":
        return "running"
    if state == "success":
        return "success"
    if state in ("failure", "error"):
        return "failure"
    return None


def review_state(meta, head):
    """Map the scoreboard meta at the current head to a sink-agnostic review state.

    The authoritative signal is the durable per-rubric `states` map, NOT the latest round's `runs`:
    a reply/partial round re-runs only some rubrics, so `runs` can show an approve for one rubric
    while another is still blocking in `states`. This mirrors the worker's `ledger_blocking` and the
    signal CI's merge close reads, so they agree. `runs` is used only as a fallback for a legacy
    scoreboard with no `states` map. State not at the current head (a fix landed since the last
    review) reads as "running, green so far".

        "none"     nothing posted yet          (Zulip 👀 / label awaiting-review)
        "running"  behind HEAD, or undecided    (Zulip ▶️ / label awaiting-review)
        "changes"  at HEAD, a blocking rubric   (Zulip ✍️ / label awaiting-author)
        "approved" at HEAD, every rubric green  (Zulip ✔️ / label ready-to-merge)
    """
    if not meta:
        return "none"
    if str(meta.get("head_sha") or "") != head:
        return "running"
    states = meta.get("states") or {}
    if states:
        # A rubric blocks unless it is green or stale (a carried-forward approval), per ledger_blocking.
        if any(v not in ("green", "stale") for v in states.values()):
            return "changes"
        # Ready only when every rubric is freshly green (conservative: a stale/carried state waits).
        if all(v == "green" for v in states.values()):
            return "approved"
        return "running"
    runs = meta.get("runs") or []
    if not runs:
        return "running"
    if any(r.get("verdict") not in ("approve", "error") for r in runs):
        return "changes"
    if all(r.get("verdict") == "approve" for r in runs):
        return "approved"
    return "running"


def derive(pr, ci_override=None, state=None, now=None):
    """The canonical status of a PR, as a dict:

        {"lifecycle": "open"|"merged"|"closed",
         "ci":        "running"|"success"|"failure"|None,   # None => not reported
         "review":    "none"|"running"|"changes"|"approved"|None,
         "review_inprogress": bool,                          # a live in-progress marker at HEAD
         "head":      "<sha>", "title": "<title>"}

    `ci`, `review`, and `review_inprogress` are only meaningful while the PR is open; on a
    merged/closed PR they are None/False (a sink shows a terminal state and clears the rest).

    `ci_override` (running|success|failure|none|None) forces the CI state instead of reading the
    `build` commit status. `state` lets a caller pass a pre-fetched pr_state() so the PR is read
    once (a Zulip sink creates its message from the title BEFORE these fallible reads). `now`
    (epoch seconds) is the clock for the in-progress TTL; defaults to the wall clock.
    """
    st = state if state is not None else pr_state(pr)
    if st["merged"]:
        lifecycle = "merged"
    elif st["state"] == "closed":
        lifecycle = "closed"
    else:
        lifecycle = "open"

    if lifecycle != "open":
        ci = None
        review = None
        inprogress = False
    else:
        if ci_override is not None:
            ci = None if ci_override == "none" else ci_override
        else:
            ci = ci_status(st["head"])
        comments = trusted_comments(pr)
        review = review_state(scoreboard_meta_from(comments), st["head"])
        inprogress = inprogress_from(comments, st["head"], int(time.time()) if now is None else now)

    return {
        "lifecycle": lifecycle,
        "ci": ci,
        "review": review,
        "review_inprogress": inprogress,
        "head": st["head"],
        "title": st["title"],
    }
