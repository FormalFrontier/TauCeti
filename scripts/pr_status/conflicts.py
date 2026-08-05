#!/usr/bin/env python3
"""Notice, announce, and time-stamp merge conflicts on open TauCeti PRs.

A PR becomes conflicted when `main` moves, not when its author does anything.
That is the whole problem this module exists for: every other trigger in this
repository is scoped to the PR (`pull_request_target`, a `pr-build` /
`Review` `workflow_run`, an `issue_comment`), so the one transition an author
most needs to hear about was the one transition that fired NOTHING. A PR could
go from mergeable to conflicting and back to nobody's attention: no label, no
Zulip reaction, no comment, no alert. `stuck_alerts.py` deliberately skips a
conflicting PR (it is not being wrongly withheld by the merge path), and
`housekeeping.py` only retires a PR that is *blocking under review*, so a
conflicted-but-approved PR was reaped by nothing either. It simply rotted.

This module closes that gap and nothing more. It does not rebase anything and it
does not nag: it makes the conflict visible, exactly once per episode, in the
three places an author already looks.

  1. **A marker comment on the PR** -- the only one of the three that generates a
     GitHub notification, so it is what actually reaches an author whose session
     has moved on. One comment per conflict *episode*, carrying a hidden
     `<!--tauceti-conflict:v1 {...}-->` marker; edited (never re-posted) to a ✅
     form when the PR merges cleanly again, and re-posted fresh if the PR
     conflicts a second time, so a recurrence is genuinely seen. Every write is
     gated on a fresh confirmation that the head, the base, and the mergeability
     are all still what the sweep saw, so a push landing mid-sweep cannot produce
     a comment about a state the PR has already left.
  2. **The `merge-conflict` label**, via `labels.py` -- which stays the sole
     writer of the status labels, so the "exactly one" invariant is unaffected.
  3. **The ⚠️ Zulip reaction**, via `zulip.py`, on the PR's existing post.

The marker also makes the problem MEASURABLE. Its JSON records `onset` and, once
cleared, `resolved` (epoch seconds), so conflict-to-resolution is a plain read of
the PR's own comments -- plus, for an episode nobody was told about, of the
`merge-conflict` label's timeline -- via `conflicts.py report`. Before this, the
only way to get that number was to replay every PR head against every `main`
commit with `git merge-tree`. The target that motivated this, a median under 24h,
is not something you can chase without being able to re-measure it cheaply.

Mergeability is read for EVERY open PR in one GraphQL query. The per-PR cost after
that is one paginated comment read each, deliberately: the marker comments ARE the
state, and short-circuiting on the `merge-conflict` label instead would mean a lost
label silently swallows the next conflict notice -- the one failure this module must
not have. At this repository's rate (a couple of sweeps an hour over ~50 open PRs)
that is ~100 requests an hour against a 5000/hour budget. Beyond that only two kinds
of PR cost anything: one whose comment state just changed, and one that is currently
conflicting, whose label and reaction are re-asserted every sweep. The latter is
deliberate -- during an episode nothing else fires for that PR, so a sink lost to a
failed write would otherwise stay lost for exactly the window it exists to cover --
and it is a handful of PRs, not the queue.

GitHub computes `mergeable` lazily: the first read after the base moves schedules
a background merge and answers UNKNOWN. The sweep re-reads the unknowns a few
times, and any PR still UNKNOWN at the end is LEFT EXACTLY AS IT IS -- not
announced, not cleared. "We could not compute it" is not evidence either way, and
an hour later the next sweep will know.

A PR that is *permanently* UNKNOWN is a different problem and not this module's to
solve: it means GitHub has stopped recomputing mergeability at all, usually because
the PR's recorded head has diverged from its branch tip. `stuck_alerts.py`'s
`diverged-head` detector is what escalates that, so a PR this sweep can never see
is not silently dropped -- it surfaces there instead.

Usage:
    conflicts.py sweep [--dry-run] [--no-zulip]
    conflicts.py report [--json] [--days N]

`sweep` reconciles every open PR. `--dry-run` reads everything and prints what it
would do, touching no comment, label, or reaction. `--no-zulip` skips the Zulip
sink (useful locally, and implied when no bot credentials are set).

`report` reads the conflict markers back out of GitHub and prints the
conflict-to-resolution distribution -- overall and per author -- plus the
still-open conflicts and how long they have been live. `--days N` (default 30)
sets the window. It reads CLOSED and merged PRs as well as open ones: a conflict
that was resolved and then merged is precisely the case that must not be dropped,
or the median would improve every time the queue got healthier. For the same
reason it also reads the `merge-conflict` label's own timeline, which is what
records an episode that came and went while the PR was parked and so never got a
comment; those count towards the queue-wide median and are broken out separately,
since nobody was asked to act on them.

Environment:
    GH_REPO                                  default "TauCetiProject/TauCeti"
    GH_TOKEN / GITHUB_TOKEN                  used by `gh` (needs issues:write)
    ZULIP_API_KEY, ZULIP_EMAIL, ZULIP_SITE   bot credentials (optional)
    ZULIP_CHANNEL / ZULIP_TOPIC              default "Tau Ceti" / "PRs"

Only python3's standard library and an authenticated `gh` CLI are required.

Run status follows the same philosophy as the other sinks in this package: the
COMMENTS are the signal, not the run's red/green. A transient per-PR failure is
logged and the sweep continues; the run exits non-zero only if it could not read
the PR list at all (nothing was checked) or if a write failed, since a silently
half-applied sweep is how a conflict stays unannounced.
"""

import datetime
import json
import os
import re
import statistics
import sys
import time

import core
import labels
import zulip

REPO = core.REPO

MARKER_RE = re.compile(r"<!--tauceti-conflict:v1 (\{.*?\})-->", re.S)

# How many times to re-read the PRs GitHub answered UNKNOWN for, and how long to
# wait between rounds. The first read is what SCHEDULES the background merge, so
# there is always at least one re-read. The sweep's busiest moment is right after
# a push to main, when EVERY open PR needs recomputing at once, hence a budget of
# ~40s rather than a couple of seconds; whatever is still unknown after that waits
# for the hourly run.
UNKNOWN_ROUNDS = 5
UNKNOWN_WAIT_SECONDS = 10.0

# A PR carrying any of these is parked on purpose. It still gets the label and the
# reaction -- the queue view should be honest about its state -- but no comment:
# the comment is a call to action, and nobody asked for action on a parked PR.
# Mirrors stuck_alerts.HOLD_LABELS.
#
# Withholding the comment must not falsify the measurement, and that takes care:
# the comment is where the onset is recorded, so a parked conflict has no marker to
# date it by. The LABEL is the second record, and it is written whether the PR is
# parked or not -- on the moment the sweep first sees the conflict, off when it
# clears -- so GitHub's `labeled`/`unlabeled` events bracket a parked episode
# without notifying anyone. An unparked PR's notice is dated from the `labeled`
# event (`label_onset`), so a days-old conflict is not reported as minutes old, and
# an episode that both starts AND clears while parked is recovered whole by
# `unannounced_episodes`, which `report` counts towards the queue-wide median and
# breaks out separately: it is a real conflict, but not one anybody was asked to fix.
HOLD_LABELS = {"keep", "hold", "wip", "human", "do-not-close", "blocked"}

# The status label this module drives, via labels.py. Also the onset store for an
# episode that has no comment yet; see `label_onset`.
CONFLICT_LABEL = "merge-conflict"

CONFLICT_BODY = """\
⚠️ **This PR no longer merges into `main`.**

`main` has moved on since this branch was last updated, and the merge now \
conflicts. Nothing downstream can make progress until that is fixed: a green \
build and an approving review on the current head still cannot merge.

**To resolve:** rebase this branch onto current `main` (or merge `main` into it) \
and push.

Do check what the conflict actually *is* before resolving it mechanically. If \
`main` has since landed its own version of something this PR adds, part of this \
PR may be superseded, and the right answer is to drop that part -- or close the \
PR -- rather than to reconcile the text. That is an authoring decision.

This comment is posted once per conflict and edited to a ✅ when the PR merges \
cleanly again. Nothing else in the pipeline reports a conflict, so if you are \
reading this, it is the only notice you will get.

<!--tauceti-conflict:v1 {marker}-->"""

RESOLVED_BODY = """\
✅ **Merge conflict resolved** — this PR merges into `main` again.

It conflicted for {duration} ({onset} → {resolved}).

<!--tauceti-conflict:v1 {marker}-->"""


def log(msg):
    print(msg, flush=True)


def now_epoch():
    return int(time.time())


def iso(epoch):
    return datetime.datetime.fromtimestamp(
        epoch, datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")


def human_duration(seconds):
    """A compact, readable span: `3h 12m`, `2d 4h`, `41m`."""
    seconds = max(0, int(seconds))
    days, rem = divmod(seconds, 86400)
    hours, rem = divmod(rem, 3600)
    minutes = rem // 60
    if days:
        return f"{days}d {hours}h"
    if hours:
        return f"{hours}h {minutes}m"
    return f"{minutes}m"


# ----- GitHub reads -----------------------------------------------------------

OPEN_PRS_QUERY = """
query($owner:String!, $name:String!, $cursor:String) {
  repository(owner:$owner, name:$name) {
    pullRequests(states:OPEN, first:100, after:$cursor,
                 orderBy:{field:CREATED_AT, direction:ASC}) {
      pageInfo { hasNextPage endCursor }
      nodes {
        number title isDraft mergeable headRefOid baseRefOid
        author { login }
        # 100, not 50: a hold label past the page would read as absent and earn the
        # PR a comment it should never have got. Nothing here carries 100 labels.
        labels(first:100) { nodes { name } }
      }
    }
  }
}
"""


def open_prs():
    """Every open PR as {number, title, draft, mergeable, author, labels}.

    `mergeable` is GitHub's MERGEABLE / CONFLICTING / UNKNOWN, normalised to
    False / True / None (the same tri-state as `core.conflicting`). One GraphQL
    page per 100 PRs, so the whole queue costs one or two requests instead of one
    REST read per PR.
    """
    owner, _, name = REPO.partition("/")
    rows, cursor = [], None
    while True:
        page = core.graphql(OPEN_PRS_QUERY, owner=owner, name=name, cursor=cursor)
        block = page["repository"]["pullRequests"]
        for node in block["nodes"]:
            rows.append({
                "number": node["number"],
                "title": node.get("title") or "",
                "draft": bool(node.get("isDraft")),
                "conflicting": {"CONFLICTING": True, "MERGEABLE": False}.get(
                    node.get("mergeable")),
                "head": node.get("headRefOid") or "",
                "base": node.get("baseRefOid") or "",
                "author": ((node.get("author") or {}).get("login")) or "",
                "labels": [l["name"] for l in (node.get("labels") or {}).get("nodes", [])],
            })
        if not block["pageInfo"]["hasNextPage"]:
            return rows
        cursor = block["pageInfo"]["endCursor"]


def resolve_unknowns(prs, sleep=time.sleep):
    """Re-read the PRs GitHub answered UNKNOWN for, in place.

    The first read is what asks GitHub to compute the merge, so a second read a
    few seconds later usually has the answer. Whatever is still unknown after
    `UNKNOWN_ROUNDS` stays None and the caller must leave those PRs untouched.
    """
    for _ in range(UNKNOWN_ROUNDS - 1):
        pending = {p["number"] for p in prs if p["conflicting"] is None}
        if not pending:
            return
        log(f"{len(pending)} PR(s) with mergeability not yet computed; re-reading")
        sleep(UNKNOWN_WAIT_SECONDS)
        # Re-key on (number, head, base), not number alone: between rounds the
        # author may push, and an answer computed for the NEW head must not be
        # filled in as the answer for the head we recorded.
        fresh = {(p["number"], p["head"], p["base"]): p["conflicting"] for p in open_prs()}
        for pr in prs:
            answer = fresh.get((pr["number"], pr["head"], pr["base"]))
            if pr["conflicting"] is None and answer is not None:
                pr["conflicting"] = answer
    still = [p["number"] for p in prs if p["conflicting"] is None]
    if still:
        log(f"mergeability still unknown for {still}; leaving them exactly as they are")


def parse_marker(body):
    """The conflict marker's JSON object from a comment body, or None.

    A body carrying several markers (it cannot, but be explicit) uses the last
    one; a malformed payload reads as absent rather than crashing the sweep.
    """
    found = None
    for match in MARKER_RE.finditer(body or ""):
        try:
            data = json.loads(match.group(1))
        except json.JSONDecodeError:
            continue
        if isinstance(data, dict) and isinstance(data.get("onset"), int):
            found = data
    return found


def ours(comment):
    """Could this comment be one of OURS -- the automation's own marker?

    NOT `core.trusted_comments`' rule, and this distinction is load-bearing. A
    GitHub App's installation bot comments as `author_association: CONTRIBUTOR`
    (verified on this repository: `tauceti-review-bot[bot]` posts housekeeping
    comments as CONTRIBUTOR), which that rule excludes. Reading markers through it
    would mean the sweep never recognised a comment it had just written, so every
    run would post another one -- the exact spam failure the state machine exists
    to prevent, on every push to main, forever.

    So the rule here is "a bot, or a repo-associated human": `is_bot` covers the
    App under any token, and the association arm covers a maintainer running the
    sweep locally with a PAT. A fork PR author is a `User` with no repo
    association, so they still cannot forge a marker to suppress their own notice.
    """
    return bool(comment.get("is_bot")) or comment.get("association") in core.TRUSTED_ASSOC


def conflict_comments(pr):
    """This PR's conflict-marker comments, oldest first, as {id, marker, resolved}."""
    out = []
    for comment in (c for c in core.pr_comments(pr) if ours(c)):
        marker = parse_marker(comment.get("body"))
        if marker is None:
            continue
        out.append({
            "id": comment.get("id"),
            "marker": marker,
            "resolved": isinstance(marker.get("resolved"), int),
        })
    out.sort(key=lambda c: (c["marker"]["onset"], c["id"] or 0))
    return out


# ----- GitHub writes ----------------------------------------------------------

# Both writes go through `core.gh_api`, the same runner as every read here, so they
# inherit its rate-limit back-off: the sweep fires on every push to main, when the
# shared App budget is at its busiest, and losing the comment is losing the notice.
def post_comment(pr, body):
    core.gh_api(f"/repos/{REPO}/issues/{pr}/comments", method="POST", fields={"body": body})
    log(f"PR #{pr}: posted conflict notice")


def edit_comment(comment_id, body):
    core.gh_api(f"/repos/{REPO}/issues/comments/{comment_id}", method="PATCH",
                fields={"body": body})
    log(f"edited comment {comment_id} to the resolved form")


def still_true(pr, head, base, is_conflicting):
    """Re-read the PR and confirm the observation we are about to act on.

    The sweep reads the whole queue in one query and then works through it, so a
    push can land between the observation and the write. Acting on the stale value
    would post a conflict notice for a head the author has already fixed, or close
    out an episode that a NEW head has just re-opened (losing its onset). One
    targeted read immediately before the write closes that window: the head, the
    base, and the mergeability must all still agree, or we skip the PR and let the
    next sweep act on a settled state.

    Returns True only on a positive match. Anything else -- a moved head or base,
    a mergeability GitHub has gone back to computing, or a failed read -- is False,
    because "we could not confirm it" must never authorise a write.
    """
    try:
        row = core.gh_api(
            f"/repos/{REPO}/pulls/{pr}",
            jq='{head: .head.sha, base: .base.sha, mergeable: .mergeable}').strip()
    except RuntimeError as exc:
        log(f"PR #{pr}: could not re-confirm before writing ({exc}); skipping")
        return False
    if not row:
        return False
    fresh = json.loads(row.splitlines()[0])
    if fresh.get("head") != head or fresh.get("base") != base:
        log(f"PR #{pr}: head or base moved since the sweep read it; skipping")
        return False
    if not isinstance(fresh.get("mergeable"), bool):
        log(f"PR #{pr}: mergeability went back to uncomputed; skipping")
        return False
    if (not fresh["mergeable"]) != is_conflicting:
        log(f"PR #{pr}: mergeability changed since the sweep read it; skipping")
        return False
    return True


def label_events(pr):
    """Every `merge-conflict` label change on this PR as `(epoch, on)`, oldest first.

    The second record of an episode, and the only one for an episode that was never
    commented on. `sweep` labels a conflict the moment it SEES it -- parked or not --
    and takes the label off when it clears, so GitHub's own event log brackets every
    episode, at no extra write and notifying nobody. `label_onset` dates an
    unannounced episode from it and `unannounced_episodes` recovers whole ones.

    Returns None (not []) when the read fails, so a caller can tell "no such event"
    from "we could not look": the first is evidence, the second is not.
    """
    try:
        raw = core.gh_api(
            f"/repos/{REPO}/issues/{pr}/events?per_page=100",
            jq=f'.[] | select(.label.name == "{CONFLICT_LABEL}")'
               ' | select(.event == "labeled" or .event == "unlabeled")'
               ' | "\\(.created_at) \\(.event)"',
            paginate=True)
    except (RuntimeError, ValueError) as exc:
        log(f"PR #{pr}: could not read its {CONFLICT_LABEL} history ({exc})")
        return None
    out = []
    for line in (raw or "").splitlines():
        stamp, _, event = line.strip().partition(" ")
        if event in ("labeled", "unlabeled"):
            out.append((iso_to_epoch(stamp), event == "labeled"))
    out.sort()
    return out


def label_onset(pr):
    """When `merge-conflict` was most recently put on this PR (epoch), or None.

    The onset of an episode nobody has been told about yet. A parked PR is labelled
    the moment the sweep first sees the conflict but gets no comment, so if it is
    later unparked while still conflicting, dating the episode from THAT sweep would
    report a conflict of days as one of minutes and quietly shorten the median. The
    `labeled` event is the timestamp GitHub already keeps for us.

    Only ever consulted for a PR that CURRENTLY carries the label, which is what
    makes its most recent `labeled` event the current application rather than a
    stale one left by an earlier episode. A missing event or a failed read returns
    None and the caller falls back to now: the notice still goes out, only its
    timestamp is approximate. Episode *existence* is never decided by the label --
    a lost label must not swallow a notice -- only its start time.
    """
    applied = [at for at, on in (label_events(pr) or []) if on]
    return max(applied) if applied else None


def conflict_body(onset):
    return CONFLICT_BODY.format(marker=json.dumps({"onset": onset}, sort_keys=True))


def resolved_body(onset, resolved):
    return RESOLVED_BODY.format(
        duration=human_duration(resolved - onset),
        onset=iso(onset), resolved=iso(resolved),
        marker=json.dumps({"onset": onset, "resolved": resolved}, sort_keys=True))


# ----- reconcile --------------------------------------------------------------

def reconcile_pr(pr, is_conflicting, now=None, dry_run=False, parked=False,
                 head=None, base=None, conflict_labelled=False):
    """Bring one PR's conflict comment in line with its live mergeability.

    Returns the action taken: "opened", "resolved", "ongoing", "clear", "parked",
    or "stale" (the PR moved under us and the next sweep should decide).

    Every write is gated on `still_true`, so nothing is posted or resolved on an
    observation the PR has since invalidated. `head`/`base` are the OIDs the sweep
    saw; passing neither skips the re-confirmation, which only a caller that has
    just read the PR itself should do.

    Draft PRs are reconciled like any other: a draft that conflicts is still a
    conflict its author has to fix, and the label/Zulip sinks already show draft
    status separately. A `parked` PR (one carrying a hold label) is left without a
    comment, but an episode already open on it is still closed out, so its
    recorded duration stays truthful.

    `conflict_labelled` says the PR already carries `merge-conflict`, i.e. an
    earlier sweep saw this conflict but left no comment (it was parked then, or the
    comment was deleted). The episode is then dated from the label rather than from
    this moment; see `label_onset`.
    """
    now = now_epoch() if now is None else now
    history = conflict_comments(pr)
    live = history[-1] if history and not history[-1]["resolved"] else None

    def confirmed():
        if dry_run or head is None or base is None:
            return True
        return still_true(pr, head, base, is_conflicting)

    if is_conflicting:
        if live is not None:
            # Ongoing. Leave the comment byte-identical: an edit notifies nobody
            # and a repost would be a nag, and this module is not a nag. No write,
            # so nothing to re-confirm.
            return "ongoing"
        if parked:
            return "parked"
        if not confirmed():
            return "stale"
        onset = min(label_onset(pr) or now, now) if conflict_labelled else now
        log(f"PR #{pr}: NEW conflict"
            + ("" if onset == now else f", first seen {iso(onset)}"))
        if not dry_run:
            post_comment(pr, conflict_body(onset))
        return "opened"

    if live is None:
        return "clear"
    if not confirmed():
        return "stale"
    onset = live["marker"]["onset"]
    log(f"PR #{pr}: conflict resolved after {human_duration(now - onset)}")
    if not dry_run:
        edit_comment(live["id"], resolved_body(onset, now))
    return "resolved"


def sweep(dry_run=False, use_zulip=True, sleep=time.sleep):
    """Reconcile every open PR. Returns the number of write failures."""
    prs = open_prs()
    resolve_unknowns(prs, sleep=sleep)
    known = [p for p in prs if p["conflicting"] is not None]
    conflicted = [p for p in known if p["conflicting"]]
    log(f"{len(prs)} open PR(s); {len(conflicted)} conflicting, "
        f"{len(prs) - len(known)} not computable this run")

    zulip_sink = _zulip_sink() if use_zulip else None
    failures = 0
    for pr in known:
        number = pr["number"]
        parked = bool(HOLD_LABELS.intersection(n.lower() for n in pr["labels"]))
        labelled = CONFLICT_LABEL in pr["labels"]
        try:
            action = reconcile_pr(number, pr["conflicting"], dry_run=dry_run,
                                  parked=parked, head=pr["head"], base=pr["base"],
                                  conflict_labelled=labelled)
        except Exception as exc:
            log(f"PR #{number}: conflict comment failed: {exc}")
            failures += 1
            continue
        if action == "stale":
            continue  # the PR moved; next sweep renders it from a settled read
        # Both sinks are convergent, so re-rendering one that already agrees costs
        # reads and no writes. A PR we see CONFLICTING is re-rendered on EVERY
        # sweep: for the whole of an episode nothing else fires for that PR -- that
        # is this module's entire premise -- so a label or a ⚠️ lost to a failed
        # write would otherwise stay lost until the conflict cleared, which is
        # exactly the window it is meant to be visible in. Off an episode the PR is
        # mergeable and its own events reconcile it (a push runs `pr-build`, which
        # refreshes Zulip), so there we pay only for a PR whose comment state just
        # changed or whose label disagrees with what we measured.
        label_wrong = labelled != bool(pr["conflicting"])
        if pr["conflicting"] or action in ("opened", "resolved") or label_wrong:
            failures += _render(number, pr["conflicting"], zulip_sink, dry_run)
    return failures


def _render(pr, is_conflicting, zulip_sink, dry_run):
    """Refresh the label and Zulip reaction for one PR. Returns failures (0 or 1).

    Both sinks are convergent and neither failure aborts the run. A failure is
    retried on the next sweep for as long as the PR conflicts (`sweep` re-renders
    every live conflict), and after the episode by the PR's own events, which by
    then are firing again. A failed LABEL write still counts as a failure, because
    the label is how the queue view and every `gh pr list` see the conflict. A
    failed Zulip reaction does NOT: that is cosmetic, exactly as zulip.py itself
    treats it, and a persistently broken bot is caught loudly by
    zulip-healthcheck.yml.
    """
    if dry_run:
        log(f"PR #{pr}: would refresh label/reaction (conflicting={is_conflicting})")
        return 0
    failures = 0
    try:
        labels.reconcile(pr, conflict_override=is_conflicting)
    except Exception as exc:
        log(f"PR #{pr}: label refresh failed: {exc}")
        failures += 1
    if zulip_sink is not None:
        try:
            zulip.reconcile(zulip_sink, str(pr), create=False, ci_override=None,
                            conflict_override=is_conflicting)
        except Exception as exc:
            log(f"PR #{pr}: Zulip refresh failed (cosmetic): {exc}")
    return failures


def _zulip_sink():
    """An authenticated Zulip client, or None when no bot is configured.

    Unlike the dedicated Zulip workflows, missing credentials here are NOT a
    config error: the comment and the label are the notification, and the
    reaction is a convenience. A broken key still surfaces loudly in
    zulip-healthcheck.yml, which exists for exactly that.
    """
    email = (os.environ.get("ZULIP_EMAIL") or "").strip()
    api_key = (os.environ.get("ZULIP_API_KEY") or "").strip()
    site = (os.environ.get("ZULIP_SITE") or "https://leanprover.zulipchat.com").strip()
    if not (email and api_key):
        log("no Zulip credentials; skipping the reaction sink")
        return None
    return zulip.Zulip(email, api_key, site)


# ----- report -----------------------------------------------------------------

REPORT_PRS_QUERY = """
query($q:String!, $cursor:String) {
  search(query:$q, type:ISSUE, first:100, after:$cursor) {
    pageInfo { hasNextPage endCursor }
    nodes { ... on PullRequest {
      number state closedAt author { login }
    } }
  }
}
"""


def report_prs(days):
    """PRs to read markers from: every PR updated in the window, open OR closed.

    Reading only open PRs would be survivor bias of the worst kind -- a conflict
    resolved by an author who then merged the PR would VANISH from the median,
    leaving only the ones that never resolved, so the number would get worse the
    better the queue got. `days` is required for the same reason it is cheap: the
    search is bounded by an updated-at window rather than the whole history.
    """
    since = datetime.datetime.fromtimestamp(
        now_epoch() - days * 86400, datetime.timezone.utc).strftime("%Y-%m-%d")
    query = f"repo:{REPO} is:pr updated:>={since}"
    rows, cursor = [], None
    while True:
        block = core.graphql(REPORT_PRS_QUERY, q=query, cursor=cursor)["search"]
        for node in block["nodes"]:
            if not node:
                continue
            rows.append({
                "number": node["number"],
                "author": ((node.get("author") or {}).get("login")) or "",
                "closed_at": node.get("closedAt"),
            })
        if not block["pageInfo"]["hasNextPage"]:
            return rows
        cursor = block["pageInfo"]["endCursor"]


REPORT_DEFAULT_DAYS = 30


def unannounced_episodes(pr, announced, now, closed_at=None):
    """This PR's conflict episodes that no comment ever recorded.

    A parked PR is labelled but deliberately not commented on, so a conflict that
    both began AND cleared while it was parked leaves no marker. Reading only
    markers would then drop precisely the episodes nobody was chasing -- the ones
    most likely to have run long -- and quietly flatter the queue-wide median. The
    `merge-conflict` label's own `labeled`/`unlabeled` events bracket them (see
    `label_events`), which costs the report one read per PR and the sweep nothing:
    the sink that writes the label runs whether the PR is parked or not.

    `announced` is this PR's marker episodes. A label interval containing one of
    their onsets is the same episode seen twice, so it is dropped here and counted
    from the marker, which is the more precise record -- and the one whose author
    was actually asked to act.
    """
    spans, start = [], None
    for at, on in (label_events(pr) or []):
        if on:
            start = at if start is None else start
        elif start is not None:
            spans.append((start, at))
            start = None
    if start is not None:
        spans.append((start, None))
    out = []
    for onset, cleared in spans:
        if any(onset <= e["onset"] <= (cleared if cleared is not None else now)
               for e in announced):
            continue
        if cleared is not None:
            state, end = "resolved", cleared
        elif closed_at:
            state, end = "censored", iso_to_epoch(closed_at)
        else:
            state, end = "live", now
        out.append({"onset": onset, "resolved": cleared if state == "resolved" else None,
                    "seconds": max(0, end - onset), "state": state})
    return out


def episodes(days=REPORT_DEFAULT_DAYS, now=None, prs=None):
    """Every conflict episode recorded in the window, newest onset first.

    Each is `{pr, author, onset, resolved, seconds, state, announced}` where `state`
    is:

        "resolved"  the PR merged cleanly again; `seconds` is the real duration
        "live"      still conflicting on an open PR; `seconds` is its age so far
        "censored"  the PR was CLOSED while still conflicting, so it has no
                    resolution and never will. Counted and shown, but kept out of
                    the resolved median: closing a conflicted PR is an outcome,
                    not a resolution time, and averaging it in would flatter or
                    ruin the number depending on which way you squinted.

    `announced` says whether the author was told: True for an episode with a marker
    comment, False for one recovered from the label alone, which is what a parked
    PR's conflict leaves behind (`unannounced_episodes`). Both are real conflicts
    and both count towards the queue-wide latency; only the announced ones carry an
    author who was asked to act, so `summarise` reports the split rather than
    silently mixing two different questions -- or, as before, silently dropping one.
    """
    now = now_epoch() if now is None else now
    cutoff = now - days * 86400
    out = []
    for pr in (report_prs(days) if prs is None else prs):
        seen = []
        for comment in conflict_comments(pr["number"]):
            marker = comment["marker"]
            resolved = marker.get("resolved") if comment["resolved"] else None
            if resolved is not None:
                state, end = "resolved", resolved
            elif pr.get("closed_at"):
                # Unresolved marker on a closed PR: the sweep only reconciles open
                # PRs, so the episode ends, unresolved, when the PR closed.
                state, end = "censored", iso_to_epoch(pr["closed_at"])
            else:
                state, end = "live", now
            seen.append({"onset": marker["onset"], "resolved": resolved,
                         "seconds": max(0, end - marker["onset"]), "state": state})
        rows = [dict(row, announced=True) for row in seen]
        rows += [dict(row, announced=False) for row in
                 unannounced_episodes(pr["number"], seen, now, pr.get("closed_at"))]
        for row in rows:
            if row["onset"] < cutoff:
                continue
            out.append({"pr": pr["number"], "author": pr["author"], **row})
    out.sort(key=lambda e: e["onset"], reverse=True)
    return out


def iso_to_epoch(text):
    return int(datetime.datetime.fromisoformat(
        text.replace("Z", "+00:00")).timestamp())


def summarise(eps):
    """Lines of a human-readable report over `episodes()` output.

    The headline median is queue-wide -- every episode, announced or not -- because
    that is the quantity the 24h target names. The unannounced ones (a conflict that
    came and went while the PR was parked) are then broken out with their own
    median, since they are the only population with no author latency in them:
    nobody was told, so nobody was slow.
    """
    lines = []
    resolved = [e for e in eps if e["state"] == "resolved"]
    live = [e for e in eps if e["state"] == "live"]
    censored = [e for e in eps if e["state"] == "censored"]
    parked = [e for e in eps if not e["announced"]]
    lines.append(f"{len(eps)} conflict episode(s): {len(resolved)} resolved, "
                 f"{len(live)} live, {len(censored)} closed while conflicting")
    if resolved:
        durations = [e["seconds"] for e in resolved]
        over = sum(1 for d in durations if d > 86400)
        lines.append(f"  resolved: median {human_duration(statistics.median(durations))}, "
                     f"max {human_duration(max(durations))}, {over} over 24h")
    if parked:
        quiet = [e["seconds"] for e in parked if e["state"] == "resolved"]
        told = [e["seconds"] for e in resolved if e["announced"]]
        detail = (f", median {human_duration(statistics.median(quiet))}" if quiet else "")
        lines.append(f"  parked:   {len(parked)} episode(s) were never announced "
                     f"(the PR was on hold, so no comment was posted){detail}")
        if quiet and told:
            lines.append(f"            announced episodes alone resolve in a median of "
                         f"{human_duration(statistics.median(told))}")
    if live:
        ages = [e["seconds"] for e in live]
        lines.append(f"  live:     median age {human_duration(statistics.median(ages))}, "
                     f"oldest {human_duration(max(ages))}")
    if censored:
        lines.append(f"  censored: {len(censored)} PR(s) were closed still conflicting; "
                     f"they have no resolution time and are not in the median")
    by_author = {}
    for e in eps:
        by_author.setdefault(e["author"], []).append(e)
    for author in sorted(by_author):
        rows = by_author[author]
        done = [e["seconds"] for e in rows if e["state"] == "resolved"]
        open_now = [e for e in rows if e["state"] == "live"]
        detail = f"{len(rows)} episode(s)"
        if done:
            detail += f", median {human_duration(statistics.median(done))}"
        if open_now:
            detail += f", {len(open_now)} still live " \
                      f"(oldest {human_duration(max(e['seconds'] for e in open_now))})"
        lines.append(f"  {author}: {detail}")
    for e in live:
        who = e["author"] + ("" if e["announced"] else ", never announced")
        lines.append(f"  LIVE #{e['pr']} ({who}) conflicting for "
                     f"{human_duration(e['seconds'])}, since {iso(e['onset'])}")
    return lines


def main(argv):
    cmd = argv[1] if len(argv) > 1 else None
    rest = argv[2:]
    if cmd == "sweep":
        dry_run = "--dry-run" in rest
        use_zulip = "--no-zulip" not in rest
        failures = sweep(dry_run=dry_run, use_zulip=use_zulip)
        if failures:
            log(f"conflict sweep: {failures} write(s) failed")
            return 1
        return 0
    if cmd == "report":
        days = REPORT_DEFAULT_DAYS
        if "--days" in rest:
            days = int(rest[rest.index("--days") + 1])
        eps = episodes(days=days)
        if "--json" in rest:
            json.dump(eps, sys.stdout, indent=2)
            print()
        else:
            for line in summarise(eps):
                print(line)
        return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
