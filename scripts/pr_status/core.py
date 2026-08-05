#!/usr/bin/env python3
"""Shared derivation of a TauCeti PR's status from GitHub truth.

This is the single place that reads what a PR's status *is* -- its lifecycle
(open / merged / closed), its `build` CI state, whether it currently conflicts
with the base branch, and its review state (from the canonical
`<!--tauceti-scoreboard-->` comment's meta JSON), plus whether a review is in
flight right now (from the engine's `<!--tauceti-review-in-progress-->` marker).
Every status *sink* imports it and renders that one truth its own way:

  * zulip.py     -> two independent groups of emoji reactions on the PR's message
  * labels.py    -> exactly one of the six status labels on the PR itself
  * conflicts.py -> one marker comment per conflict episode, which is what
                    actually notifies the author (and records the onset time)

Keeping the derivation here means the two sinks can never disagree about what a
PR's state is: they read the same `derive()` and only differ in how they show it.

Everything here reads only trusted GitHub data. The two review signals -- the
scoreboard meta and the in-progress marker -- are taken only from comments by a
repo-associated author (OWNER/MEMBER/COLLABORATOR), so a fork PR author cannot
forge review state. Both are extracted from ONE comment fetch.

The module is a pure library -- importing it has no side effects, decides nothing
on its own, and needs only python3's standard library plus an authenticated `gh`
CLI (via GH_TOKEN / GITHUB_TOKEN). It derives status from GitHub and never touches
Zulip. `run_gh` is also the one place anything here shells out to `gh`, so the
sinks' own writes (a label, a conflict comment) share its rate-limit back-off
rather than each growing a subprocess wrapper of its own.
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
TRUSTED_ASSOC = ("OWNER", "MEMBER", "COLLABORATOR")

# `gh` exits nonzero on a rate limit without retrying. These substrings identify
# that case in its stderr, so run_gh can back off instead of failing the caller.
_RATE_LIMITED = ("rate limit", "secondary rate", "API rate limit exceeded",
                 "was submitted too quickly", "HTTP 429")
RATE_LIMIT_RETRIES = 4
RATE_LIMIT_BACKOFF_SECONDS = 15
# The short ladder for `retry_transient`: 1s, 2s, 4s. A 502 clears in a moment or
# not at all, so waiting a rate limit's 15s for one only lengthens the run.
TRANSIENT_BACKOFF_SECONDS = 1


# ----- GitHub truth (via the gh CLI, authenticated by GH_TOKEN) ---------------

def run_gh(args, describe, sleep=time.sleep, retry_transient=False):
    """One `gh` call, with a bounded back-off for a rate limit.

    The single place this repository shells out to `gh`: every read, write, and
    GraphQL query below goes through it, so the back-off cannot be bypassed by
    adding a caller.

    `gh` does not retry a 403/429 rate limit of its own accord, and every sink in
    this package shares one App installation budget with the review and merge
    workflows. Failing the whole run because a burst of merges used the budget for
    a minute is the wrong answer, so a rate-limited call waits and retries a few
    times; anything else fails immediately, as before.

    `retry_transient` widens that to ANY failure, which is the policy a long bulk
    read wants: `pr_stats_graphs.py` makes thousands of GraphQL calls in one run,
    where a single 502 would otherwise throw the whole run away. The status sinks
    here leave it False deliberately -- a sweep that cannot read one PR should fail
    that PR now and let the next run act on a settled state, not paper over it.
    """
    for attempt in range(RATE_LIMIT_RETRIES):
        out = subprocess.run(["gh", *args], capture_output=True, text=True)
        if out.returncode == 0:
            return out.stdout
        stderr = out.stderr.strip()
        limited = any(marker.lower() in stderr.lower() for marker in _RATE_LIMITED)
        if not (limited or retry_transient) or attempt + 1 == RATE_LIMIT_RETRIES:
            raise RuntimeError(f"{describe} failed: {stderr}")
        delay = (RATE_LIMIT_BACKOFF_SECONDS if limited
                 else TRANSIENT_BACKOFF_SECONDS) * (2 ** attempt)
        print(f"{describe}: {'rate-limited' if limited else 'transient failure'};"
              f" retrying in {delay}s", flush=True)
        sleep(delay)


def gh_api(path, jq=None, paginate=False, method=None, fields=None, sleep=time.sleep):
    """One REST `gh api` call, backing off a rate limit as `run_gh` describes.

    A read by default; `method` ("POST"/"PATCH"/"DELETE") and `fields` (sent as
    `-f name=value`) make it a write. A write wants the same back-off a read does,
    and can take it safely: a rate-limited call was REFUSED, so retrying it cannot
    double-post the comment it was carrying.
    """
    args = ["api", path]
    if method is not None:
        args += ["--method", method]
    if paginate:
        args.append("--paginate")
    if jq is not None:
        args += ["--jq", jq]
    for key, value in (fields or {}).items():
        args += ["-f", f"{key}={value}"]
    return run_gh(args, f"gh api {path}", sleep=sleep)


def graphql(query, sleep=time.sleep, retry_transient=False, **variables):
    """One GraphQL query, returning its `data` object.

    The GraphQL twin of `gh_api`, and the repository's single GraphQL client (the
    PR status sinks here and `pr_stats_graphs.py` both call it), so a query shares
    the same rate-limit back-off as every REST read. A variable passed as None is
    dropped, so an optional cursor needs no juggling at the call site; an `int` is
    sent as a number (`-F`) rather than a string; and an `errors` block raises,
    since GraphQL reports a failed field with HTTP 200 and a `data` that is null or
    half-filled. `retry_transient` is `run_gh`'s, for a caller whose run is long
    enough that riding out a 502 beats losing it.
    """
    args = ["api", "graphql", "-f", f"query={query}"]
    for key, value in variables.items():
        if value is None:
            continue
        args += ["-F" if isinstance(value, int) else "-f", f"{key}={value}"]
    payload = json.loads(run_gh(args, "gh api graphql", sleep=sleep,
                                retry_transient=retry_transient))
    if payload.get("errors"):
        raise RuntimeError(f"GitHub GraphQL errors: {payload['errors']}")
    return payload["data"]


def _roadmap_labels(labels):
    """Sorted `roadmap/...` names from REST label objects or plain label names."""
    names = [label.get("name", "") if isinstance(label, dict) else str(label)
             for label in labels]
    return sorted(name for name in names if name.startswith("roadmap/"))


def pr_state(pr):
    """{'state','merged','head','title','author','roadmaps','mergeable'} for the PR.

    Prefer the triggering event's payload, passed in via PR_STATE/PR_HEAD/
    PR_MERGED/PR_TITLE/PR_AUTHOR/PR_LABELS_JSON (a workflow that has the
    pull_request object can set these from github.event.pull_request, so a
    close/merge needs no GitHub API call at all). Fall back to the REST API when
    PR state/head aren't set (the workflow_run and issue_comment triggers, and
    the backfill), where the payload is absent or isn't the PR we're
    reconciling.

    `mergeable` is GitHub's tri-state (True / False / None-for-not-yet-computed).
    The REST path gets it for free from the same read; the payload path has no
    trustworthy value for it and reports None, which `conflicting()` then resolves
    with one targeted read.
    """
    env_state = os.environ.get("PR_STATE")
    env_head = os.environ.get("PR_HEAD")
    if env_state and env_head:
        try:
            labels = json.loads(os.environ.get("PR_LABELS_JSON") or "[]")
        except json.JSONDecodeError:
            labels = []
        if not isinstance(labels, list):
            labels = []
        return {
            "state": env_state,
            "merged": os.environ.get("PR_MERGED") == "true",
            "head": env_head,
            "title": os.environ.get("PR_TITLE") or f"PR #{pr}",
            "author": os.environ.get("PR_AUTHOR") or "",
            "roadmaps": _roadmap_labels(labels),
            "mergeable": None,
        }
    d = json.loads(gh_api(f"/repos/{REPO}/pulls/{pr}"))
    mergeable = d.get("mergeable")
    return {
        "state": d["state"],                 # "open" | "closed"
        "merged": bool(d.get("merged")),
        "head": d["head"]["sha"],
        "title": d.get("title") or f"PR #{pr}",
        "author": (d.get("user") or {}).get("login") or "",
        "roadmaps": _roadmap_labels(d.get("labels") or []),
        "mergeable": mergeable if isinstance(mergeable, bool) else None,
    }


def trusted_comments(pr):
    """Issue comments authored by a repo-associated account (OWNER/MEMBER/COLLABORATOR).

    The review signals below read only these, so an untrusted fork-PR comment can never forge
    review state. Note what this deliberately EXCLUDES: a GitHub App's installation bot comments
    as `CONTRIBUTOR`, so a comment the automation itself posted is *not* trusted here. That is
    correct for a review verdict (the App does not issue verdicts) but wrong for a marker the
    automation wrote and must find again, which is why conflicts.py reads `pr_comments` and applies
    its own rule.
    """
    return [c for c in pr_comments(pr) if c["association"] in TRUSTED_ASSOC]


def pr_comments(pr):
    """Every issue comment on the PR, as `[{'id','body','updated','association','is_bot'}]`.

    One paginated fetch shared by both trust policies above. `id` is what lets a caller EDIT the
    comment it found (conflicts.py edits its marker to a resolved form), and `is_bot` distinguishes
    a GitHub App / bot author from a human, which `author_association` alone cannot: an installation
    bot reports `CONTRIBUTOR`, indistinguishable from an outside contributor by association. A fork
    PR author is always a `User`, so `is_bot` is a boundary they cannot cross. The jq emits one
    compact object per line (valid JSONL across any number of pages)."""
    out = gh_api(
        f"/repos/{REPO}/issues/{pr}/comments?per_page=100",
        jq='.[] | {id: .id, body: .body, updated: .updated_at,'
           ' association: .author_association, is_bot: (.user.type == "Bot")}',
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


# GitHub computes `mergeable` LAZILY: the first read of a PR whose base has moved
# schedules a background merge and answers `null`. A second read a moment later
# almost always has the answer, so re-read a null a few times before giving up.
MERGEABLE_POLLS = 3
MERGEABLE_POLL_SECONDS = 2.0


def conflicting(pr, state=None, sleep=time.sleep):
    """True / False / None -- does the PR conflict with its base branch?

    None means "GitHub has not computed it yet", NOT "no conflict". Every caller
    must treat None as *unknown* and change nothing: announcing a conflict we are
    not sure of is as wrong as clearing one that is still live.

    `state` may be a pre-fetched `pr_state()`; its `mergeable` is used when GitHub
    already answered (the REST path), so the common case costs no extra request.
    """
    if state is not None and isinstance(state.get("mergeable"), bool):
        return not state["mergeable"]
    for attempt in range(MERGEABLE_POLLS):
        raw = gh_api(f"/repos/{REPO}/pulls/{pr}", jq=".mergeable").strip()
        if raw == "true":
            return False
        if raw == "false":
            return True
        if attempt + 1 < MERGEABLE_POLLS:
            sleep(MERGEABLE_POLL_SECONDS)
    return None


def review_state(meta, head):
    """Map the scoreboard meta at the current head to a sink-agnostic review state.

    The authoritative signal is the durable per-rubric `states` map, NOT the latest round's `runs`:
    a reply/partial round re-runs only some rubrics, so `runs` can show an approve for one rubric
    while another is still blocking in `states`. This mirrors the worker's `ledger_blocking` and the
    signal CI's merge close reads, so they agree. `runs` is used only as a fallback for a legacy
    scoreboard with no `states` map. State not at the current head (a fix landed since the last
    review) reads as "running, green so far".

        "none"     nothing posted yet          (no Zulip review emoji / label awaiting-review)
        "running"  behind HEAD, or undecided    (no Zulip review emoji / label awaiting-review)
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


def derive(pr, ci_override=None, state=None, now=None, conflict_override=None):
    """The canonical status of a PR, as a dict:

        {"lifecycle": "open"|"merged"|"closed",
         "ci":        "running"|"success"|"failure"|None,   # None => not reported
         "conflicting": True|False|None,                     # None => not computed yet
         "review":    "none"|"running"|"changes"|"approved"|None,
         "review_inprogress": bool,                          # a live in-progress marker at HEAD
         "head":      "<sha>", "title": "<title>"}

    `ci`, `conflicting`, `review`, and `review_inprogress` are only meaningful while the PR is
    open; on a merged/closed PR they are None/False (a sink shows a terminal state and clears the
    rest).

    `ci_override` (running|success|failure|none|None) forces the CI state instead of reading the
    `build` commit status. `conflict_override` (True/False/None) likewise forces the conflict state,
    so the sweep -- which already read every open PR's mergeability in one GraphQL query -- does not
    re-read it per PR. `state` lets a caller pass a pre-fetched pr_state() so the PR is read
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
        conflict = None
        review = None
        inprogress = False
    else:
        if ci_override is not None:
            ci = None if ci_override == "none" else ci_override
        else:
            ci = ci_status(st["head"])
        conflict = conflict_override if conflict_override is not None else conflicting(pr, st)
        comments = trusted_comments(pr)
        review = review_state(scoreboard_meta_from(comments), st["head"])
        inprogress = inprogress_from(comments, st["head"], int(time.time()) if now is None else now)

    return {
        "lifecycle": lifecycle,
        "ci": ci,
        "conflicting": conflict,
        "review": review,
        "review_inprogress": inprogress,
        "head": st["head"],
        "title": st["title"],
    }
