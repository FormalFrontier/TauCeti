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
     conflicts a second time, so a recurrence is genuinely seen -- but not within
     `RECURRENCE_COOLDOWN_SECONDS` of the last one, so a flapping mergeability
     computation cannot turn into a stream of comments.
  2. **The `merge-conflict` label**, via `labels.py` -- which stays the sole
     writer of the status labels, so the "exactly one" invariant is unaffected.
  3. **The ⚠️ Zulip reaction**, via `zulip.py`, on the PR's existing post.

The marker also makes the problem MEASURABLE. Its JSON records `onset` and, once
cleared, `resolved` (epoch seconds), so conflict-to-resolution is a plain read of
the PR's own comments -- `conflicts.py report`. Before this, the only way to get
that number was to replay every PR head against every `main` commit with
`git merge-tree` (which is what `conflict_stats.py` does for the historical
baseline). The target that motivated this, a median under 24h, is not something
you can chase without being able to re-measure it cheaply.

Mergeability is read for EVERY open PR in one GraphQL query. The per-PR cost after
that is one paginated comment read each, deliberately: the marker comments ARE the
state, and short-circuiting on the `merge-conflict` label instead would mean a lost
label silently swallows the next conflict notice -- the one failure this module must
not have. At this repository's rate (a couple of sweeps an hour over ~50 open PRs)
that is ~100 requests an hour against a 5000/hour budget. Only the PRs that actually
changed state cost anything more.

GitHub computes `mergeable` lazily: the first read after the base moves schedules
a background merge and answers UNKNOWN. The sweep re-reads the unknowns a few
times, and any PR still UNKNOWN at the end is LEFT EXACTLY AS IT IS -- not
announced, not cleared. "We could not compute it" is not evidence either way, and
an hour later the next sweep will know.

Usage:
    conflicts.py sweep [--dry-run] [--no-zulip]
    conflicts.py report [--json] [--days N]

`sweep` reconciles every open PR. `--dry-run` reads everything and prints what it
would do, touching no comment, label, or reaction. `--no-zulip` skips the Zulip
sink (useful locally, and implied when no bot credentials are set).

`report` reads the conflict markers back out of GitHub and prints the
conflict-to-resolution distribution -- overall and per author -- plus the
still-open conflicts and how long they have been live. `--days N` limits it to
episodes that began in the last N days.

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
import subprocess
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
HOLD_LABELS = {"keep", "hold", "wip", "human", "do-not-close", "blocked"}

# How soon after clearing a conflict a PR may open a NEW episode. A conflict that
# reappears within half an hour is either GitHub flapping its own computation or a
# push that did not take, and in both cases the author was told about it minutes
# ago -- a second comment would be noise, and comment spam is the worst way for an
# autonomous notifier to fail. A genuine recurrence just waits for the next sweep:
# the label and the reaction show it immediately either way.
RECURRENCE_COOLDOWN_SECONDS = 1800

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
        number title isDraft mergeable
        author { login }
        labels(first:50) { nodes { name } }
      }
    }
  }
}
"""


def _graphql(query, **variables):
    cmd = ["gh", "api", "graphql", "-f", f"query={query}"]
    for key, value in variables.items():
        cmd += ["-f", f"{key}={value}"]
    out = subprocess.run(cmd, capture_output=True, text=True)
    if out.returncode != 0:
        raise RuntimeError(f"gh api graphql failed: {out.stderr.strip()}")
    return json.loads(out.stdout)


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
        page = _graphql(OPEN_PRS_QUERY, owner=owner, name=name,
                        **({"cursor": cursor} if cursor else {}))
        block = page["data"]["repository"]["pullRequests"]
        for node in block["nodes"]:
            rows.append({
                "number": node["number"],
                "title": node.get("title") or "",
                "draft": bool(node.get("isDraft")),
                "conflicting": {"CONFLICTING": True, "MERGEABLE": False}.get(
                    node.get("mergeable")),
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
        fresh = {p["number"]: p["conflicting"] for p in open_prs()}
        for pr in prs:
            if pr["conflicting"] is None and fresh.get(pr["number"]) is not None:
                pr["conflicting"] = fresh[pr["number"]]
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


def conflict_comments(pr):
    """This PR's conflict-marker comments, oldest first, as {id, marker, resolved}.

    Read through `core.trusted_comments`, so only a repo-associated author's
    comment counts -- the same trust the review scoreboard and the in-progress
    marker use. A fork PR author cannot post a marker that suppresses their own
    conflict notice.
    """
    out = []
    for comment in core.trusted_comments(pr):
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

def _gh(args):
    result = subprocess.run(["gh", "api", *args], capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"gh api {' '.join(args)} failed: {result.stderr.strip()}")
    return result.stdout


def post_comment(pr, body):
    _gh(["--method", "POST", f"/repos/{REPO}/issues/{pr}/comments", "-f", f"body={body}"])
    log(f"PR #{pr}: posted conflict notice")


def edit_comment(comment_id, body):
    _gh(["--method", "PATCH", f"/repos/{REPO}/issues/comments/{comment_id}",
         "-f", f"body={body}"])
    log(f"edited comment {comment_id} to the resolved form")


def conflict_body(onset):
    return CONFLICT_BODY.format(marker=json.dumps({"onset": onset}, sort_keys=True))


def resolved_body(onset, resolved):
    return RESOLVED_BODY.format(
        duration=human_duration(resolved - onset),
        onset=iso(onset), resolved=iso(resolved),
        marker=json.dumps({"onset": onset, "resolved": resolved}, sort_keys=True))


# ----- reconcile --------------------------------------------------------------

def reconcile_pr(pr, is_conflicting, now=None, dry_run=False, parked=False):
    """Bring one PR's conflict comment in line with its live mergeability.

    Returns the action taken: "opened", "resolved", "ongoing", "clear", "parked",
    or "cooldown".

    Draft PRs are reconciled like any other: a draft that conflicts is still a
    conflict its author has to fix, and the label/Zulip sinks already show draft
    status separately. A `parked` PR (one carrying a hold label) is left without a
    comment, but an episode already open on it is still closed out, so its
    recorded duration stays truthful.
    """
    now = now_epoch() if now is None else now
    history = conflict_comments(pr)
    live = history[-1] if history and not history[-1]["resolved"] else None

    if is_conflicting:
        if live is not None:
            # Ongoing. Leave the comment byte-identical: an edit notifies nobody
            # and a repost would be a nag, and this module is not a nag.
            return "ongoing"
        if parked:
            return "parked"
        if history and now - history[-1]["marker"]["resolved"] < RECURRENCE_COOLDOWN_SECONDS:
            log(f"PR #{pr}: conflicting again within the cooldown; not re-commenting yet")
            return "cooldown"
        log(f"PR #{pr}: NEW conflict")
        if not dry_run:
            post_comment(pr, conflict_body(now))
        return "opened"

    if live is None:
        return "clear"
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
        try:
            action = reconcile_pr(number, pr["conflicting"], dry_run=dry_run,
                                  parked=parked)
        except Exception as exc:
            log(f"PR #{number}: conflict comment failed: {exc}")
            failures += 1
            continue
        # The label and reaction are cheap to keep converged but not free, so only
        # touch a PR whose comment state just changed or whose label disagrees with
        # what we just measured. An unchanged, correctly-labelled PR costs nothing.
        label_wrong = ("merge-conflict" in pr["labels"]) != bool(pr["conflicting"])
        if action in ("opened", "resolved") or label_wrong:
            failures += _render(number, pr["conflicting"], zulip_sink, dry_run)
    return failures


def _render(pr, is_conflicting, zulip_sink, dry_run):
    """Refresh the label and Zulip reaction for one PR. Returns failures (0 or 1).

    Both sinks are convergent, so a failure here self-heals on the next sweep and
    never aborts the run. A failed LABEL write still counts, because the label is
    how the queue view and every `gh pr list` see the conflict. A failed Zulip
    reaction does NOT: that is cosmetic, exactly as zulip.py itself treats it, and
    a persistently broken bot is caught loudly by zulip-healthcheck.yml.
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

def episodes(days=None, now=None):
    """Every conflict episode recorded on an open PR, newest onset first.

    Each is `{pr, author, onset, resolved, seconds, live}`. A live episode has
    `resolved` None and `seconds` measured to `now`, so "how long has this been
    conflicting" and "how long did that conflict last" are the same number.

    This reads only OPEN PRs: once a PR merges its episodes are history, and the
    question the report answers is whether the queue is currently healthy.
    """
    now = now_epoch() if now is None else now
    cutoff = None if days is None else now - days * 86400
    out = []
    for pr in open_prs():
        for comment in conflict_comments(pr["number"]):
            marker = comment["marker"]
            onset = marker["onset"]
            if cutoff is not None and onset < cutoff:
                continue
            resolved = marker.get("resolved") if comment["resolved"] else None
            out.append({
                "pr": pr["number"],
                "author": pr["author"],
                "onset": onset,
                "resolved": resolved,
                "seconds": (resolved or now) - onset,
                "live": resolved is None,
            })
    out.sort(key=lambda e: e["onset"], reverse=True)
    return out


def median(values):
    if not values:
        return None
    ordered = sorted(values)
    mid = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[mid]
    return (ordered[mid - 1] + ordered[mid]) / 2


def summarise(eps):
    """Lines of a human-readable report over `episodes()` output."""
    lines = []
    resolved = [e for e in eps if not e["live"]]
    live = [e for e in eps if e["live"]]
    lines.append(f"{len(eps)} conflict episode(s): {len(resolved)} resolved, {len(live)} live")
    if resolved:
        durations = [e["seconds"] for e in resolved]
        lines.append(f"  resolved: median {human_duration(median(durations))}, "
                     f"max {human_duration(max(durations))}")
    if live:
        ages = [e["seconds"] for e in live]
        lines.append(f"  live:     median age {human_duration(median(ages))}, "
                     f"oldest {human_duration(max(ages))}")
    by_author = {}
    for e in eps:
        by_author.setdefault(e["author"], []).append(e)
    for author in sorted(by_author):
        rows = by_author[author]
        done = [e["seconds"] for e in rows if not e["live"]]
        open_now = [e for e in rows if e["live"]]
        detail = f"{len(rows)} episode(s)"
        if done:
            detail += f", median {human_duration(median(done))}"
        if open_now:
            detail += f", {len(open_now)} still live " \
                      f"(oldest {human_duration(max(e['seconds'] for e in open_now))})"
        lines.append(f"  {author}: {detail}")
    for e in live:
        lines.append(f"  LIVE #{e['pr']} ({e['author']}) conflicting for "
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
        days = None
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
