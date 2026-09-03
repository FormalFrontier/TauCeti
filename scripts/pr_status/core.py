#!/usr/bin/env python3
"""Shared derivation of a TauCeti PR's status from GitHub truth.

This is the single place that reads what a PR's status *is* -- its lifecycle
(open / merged / closed), its `build` CI state, and its review state (from the
newest `<!--tauceti-scoreboard-->` comment's meta JSON), plus whether a review is
in flight right now (from the engine's `<!--tauceti-review-in-progress-->`
marker). Every status *sink* imports it and renders that one truth its own way:

  * zulip.py   -> two independent groups of emoji reactions on the PR's message
  * labels.py  -> exactly one of the six status labels on the PR itself

Keeping the derivation here means the two sinks can never disagree about what a
PR's state is: they read the same `derive()` and only differ in how they show it.

The status sinks deliberately use the same no-author-bar policy as the worker and auto-merge: the
newest marked scoreboard counts regardless of the comment author's repository association. A review
posted by a contributor is therefore reflected in labels and Zulip instead of remaining visibly
`awaiting-review` after the worker has recorded the head as reviewed. The status labels are not a
security boundary; the build, scope, axiom and bump guards remain trusted commit statuses.

Destructive housekeeping is intentionally stricter. It calls
`repo_associated_scoreboard_meta`, which accepts only comments by OWNER/MEMBER/COLLABORATOR accounts,
so an arbitrary commenter cannot make housekeeping close somebody else's PR. Both status review
signals are extracted from one all-comments fetch.

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
_REPO_ASSOCIATED = ("OWNER", "MEMBER", "COLLABORATOR")

# `gh` exits nonzero on a rate limit without retrying. The sinks driven by
# pr-labels.yml, zulip-pr*.yml and housekeeping.yml read through gh_api against
# ONE shared App installation budget; stuck-alerts.yml runs on GITHUB_TOKEN and so
# has its own. Either way a burst of merges can spend the budget out from under
# whichever read comes next.
#
# `gh` writes the API's message followed by "(HTTP <status>)" to stderr, so a rate
# limit is recognised by STATUS first and wording second. Matching on wording alone
# would retry a 404 whose body happens to mention a rate limit.
# `gh` usually renders "<message> (HTTP <status>)", but a response with no JSON
# message is rendered bare as "gh: HTTP 429". Accept both spellings.
_HTTP_STATUS = re.compile(r"\(HTTP (\d{3})\)|\bHTTP (\d{3})\b")
_RATE_LIMIT_WORDING = ("rate limit", "abuse detection", "was submitted too quickly")

# Total calls, not retries. GitHub asks for at least a minute before retrying a
# secondary limit, so the waits are 60s then 120s -- not the sub-minute schedule a
# generic exponential back-off would use, which GitHub warns can prolong the limit.
RATE_LIMIT_ATTEMPTS = 3
SECONDARY_BACKOFF_SECONDS = 60
# A PRIMARY limit (quota exhausted) clears only at the hourly reset, which is far
# too long to sleep inside a workflow step. Past this, give up immediately and say
# when it clears rather than burning the job's timeout.
RATE_LIMIT_MAX_WAIT_SECONDS = 180


# ----- GitHub truth (via the gh CLI, authenticated by GH_TOKEN) ---------------

class RateLimited(RuntimeError):
    """A rate limit this read gave up on -- whether the retries were spent, the
    quota's reset was too far off to wait for, or an earlier call already
    established the limit. Distinct from a plain failure so a caller looping over
    many items can tell "GitHub is refusing us" from "this one item is broken"."""


# Once a limit is established, every later read is refused until it resets. Without
# this a caller that catches per-item failures — stuck_alerts runs ten detectors,
# housekeeping and the Zulip backfill loop per PR — would start the full wait again
# for each one and blow the job's timeout long before doing any work.
_BLOCKED_UNTIL = 0.0


def _rate_limited(stderr):
    """Is this stderr a rate limit? Status first, wording second."""
    found = _HTTP_STATUS.search(stderr)
    status = int(found.group(1) or found.group(2)) if found else None
    if status == 429:
        return True
    if status == 403:
        return any(word in stderr.lower() for word in _RATE_LIMIT_WORDING)
    return False


QUOTA_EXHAUSTED = "exhausted"   # the hourly budget is spent; seconds says until when
QUOTA_OK = "ok"                 # budget has room, so the refusal was a secondary limit
QUOTA_UNKNOWN = "unknown"       # the probe itself failed; assume nothing


def _quota_state():
    """(state, seconds-until-reset) for the core REST quota.

    QUOTA_UNKNOWN is deliberately distinct from QUOTA_OK. `/rate_limit` does not
    count against the PRIMARY quota, but GitHub says it can count against a
    SECONDARY one -- so the probe can itself be refused, and reading that failure
    as "the budget has room" would have us keep issuing requests while limited,
    which is what prolongs a block.
    """
    out = subprocess.run(
        ["gh", "api", "rate_limit", "--jq",
         r'"\(.resources.core.remaining) \(.resources.core.reset)"'],
        capture_output=True, text=True)
    if out.returncode != 0:
        return QUOTA_UNKNOWN, None
    try:
        remaining, reset = out.stdout.split()
        if int(remaining) > 0:
            return QUOTA_OK, None
        return QUOTA_EXHAUSTED, max(0, int(reset) - int(time.time()))
    except (TypeError, ValueError):
        return QUOTA_UNKNOWN, None


def _block_for(seconds):
    """Refuse reads for `seconds`, never shortening a block already in force: a
    short secondary hold must not overwrite a long primary one."""
    global _BLOCKED_UNTIL
    _BLOCKED_UNTIL = max(_BLOCKED_UNTIL, time.time() + seconds)


def gh_api(path, jq=None, paginate=False):
    """One `gh api` read, waiting out a rate limit within a bounded budget.

    `gh` does not retry a 403/429 of its own accord, so a burst of merges spending
    the budget failed whichever sink read next: an hourly sweep losing a run, or a
    status label left wrong until some later event fired.

    Only a rate limit is retried, and only on its own terms: at least a minute for
    a secondary limit, and for an exhausted hourly quota only when its reset is
    within RATE_LIMIT_MAX_WAIT_SECONDS -- a reset further off than that cannot be
    waited for inside a workflow step, so it raises RateLimited immediately and
    blocks later reads until it passes. Every other failure raises on the first
    attempt, so a 404 or a permission error stays as loud, and as fast, as before.

    KNOWN LIMIT: `gh api` prints the response body, not its headers, so a
    `Retry-After` GitHub sent cannot be honoured. Capturing it would mean
    `--include` and stripping a header block from every page of a paginated read,
    for a value that is usually within the minimum we already wait. The waits here
    are GitHub's documented floor, not its per-response instruction.

    The bound is on the SLEEP SCHEDULE, not on wall clock: the subprocesses
    themselves are unbounded, so a hung `gh` is not covered. Single-threaded, and
    the breaker is per process -- separate workflow jobs sharing an installation
    budget do not coordinate.
    """
    now = time.time()
    if now < _BLOCKED_UNTIL:
        raise RateLimited(
            f"gh api {path} skipped: rate limited for another "
            f"{int(_BLOCKED_UNTIL - now)}s")

    cmd = ["gh", "api", path]
    if paginate:
        cmd.append("--paginate")
    if jq is not None:
        cmd += ["--jq", jq]
    for attempt in range(RATE_LIMIT_ATTEMPTS):
        out = subprocess.run(cmd, capture_output=True, text=True)
        if out.returncode == 0:
            return out.stdout
        stderr = out.stderr.strip()
        if not _rate_limited(stderr):
            raise RuntimeError(f"gh api {path} failed: {stderr}")
        # An exhausted hourly quota clears only at its reset; a secondary limit
        # eases on its own. Probe once, and only while the answer is still useful:
        # after the last attempt there is nothing left to decide.
        state, reset_in = (_quota_state() if attempt + 1 < RATE_LIMIT_ATTEMPTS
                           else (QUOTA_UNKNOWN, None))
        if state is QUOTA_EXHAUSTED and reset_in > RATE_LIMIT_MAX_WAIT_SECONDS:
            _block_for(reset_in)
            raise RateLimited(f"gh api {path} failed: hourly quota exhausted, "
                              f"resets in {reset_in}s")
        backoff = SECONDARY_BACKOFF_SECONDS * (2 ** attempt)
        if attempt + 1 == RATE_LIMIT_ATTEMPTS:
            # Hold off for what the NEXT wait would have been, not the first one:
            # releasing after 60s would let a looping caller start the whole
            # 60/120 schedule again, which is what the breaker exists to stop.
            _block_for(backoff)
            raise RateLimited(f"gh api {path} failed after "
                              f"{RATE_LIMIT_ATTEMPTS} attempts: {stderr}")
        delay = reset_in if state is QUOTA_EXHAUSTED else backoff
        print(f"gh api rate-limited; retrying in {delay}s", flush=True)
        time.sleep(delay)


def _roadmap_labels(labels):
    """Sorted `roadmap/...` names from REST label objects or plain label names."""
    names = [label.get("name", "") if isinstance(label, dict) else str(label)
             for label in labels]
    return sorted(name for name in names if name.startswith("roadmap/"))


def pr_state(pr):
    """{'state','merged','head','title','author','roadmaps'} for the PR.

    Prefer the triggering event's payload, passed in via PR_STATE/PR_HEAD/
    PR_MERGED/PR_TITLE/PR_AUTHOR/PR_LABELS_JSON (a workflow that has the
    pull_request object can set these from github.event.pull_request, so a
    close/merge needs no GitHub API call at all). Fall back to the REST API when
    PR state/head aren't set (the workflow_run and issue_comment triggers, and
    the backfill), where the payload is absent or isn't the PR we're
    reconciling.
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
        }
    d = json.loads(gh_api(f"/repos/{REPO}/pulls/{pr}"))
    return {
        "state": d["state"],                 # "open" | "closed"
        "merged": bool(d.get("merged")),
        "head": d["head"]["sha"],
        "title": d.get("title") or f"PR #{pr}",
        "author": (d.get("user") or {}).get("login") or "",
        "roadmaps": _roadmap_labels(d.get("labels") or []),
    }


def issue_comments(pr):
    """All issue comments as `[{'body','updated','author_association'}]`.

    One paginated fetch is reused for both status review signals below. The jq emits one compact
    object per line (valid JSONL across any number of pages). Keeping the association in the neutral
    row lets destructive callers apply the stricter repository-associated policy without duplicating
    the fetch or the scoreboard parser.
    """
    out = gh_api(
        f"/repos/{REPO}/issues/{pr}/comments?per_page=100",
        jq='.[] | {body: .body, updated: .updated_at, author_association: .author_association}',
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


def repo_associated_comments(pr):
    """Only comments by OWNER/MEMBER/COLLABORATOR accounts, for destructive consumers."""
    return [c for c in issue_comments(pr) if c.get("author_association") in _REPO_ASSOCIATED]


def scoreboard_meta_from(comments):
    """The newest scoreboard comment's meta JSON ({} if none) from the supplied comment policy."""
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
    """Newest marked scoreboard from any author, matching the worker and auto-merge policy."""
    return scoreboard_meta_from(issue_comments(pr))


def repo_associated_scoreboard_meta(pr):
    """Newest marked scoreboard from a repo-associated author, for destructive consumers."""
    return scoreboard_meta_from(repo_associated_comments(pr))


def inprogress_from(comments, head, now):
    """True iff some supplied comment carries an UNEXPIRED in-progress marker for exactly `head`.

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
    per-rubric state representation auto-merge reads, although auto-merge selects scoreboards under a
    different author policy. `runs` is used only as a fallback for a legacy scoreboard with no `states`
    map. State not at the current head (a fix landed since the last
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
        comments = issue_comments(pr)
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
