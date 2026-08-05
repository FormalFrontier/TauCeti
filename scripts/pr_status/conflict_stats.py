#!/usr/bin/env python3
"""Reconstruct the history of merge conflicts in the PR queue, from git alone.

`conflicts.py report` answers "how long are conflicts lasting" from the markers
this repository now writes. This script answers the same question for the era
BEFORE those markers existed, which is the only way to establish the baseline the
target (median conflict-to-resolution under 24h) is measured against. GitHub keeps
no history of `mergeable`: it reports only the current value, and nothing in the
timeline records the moment a PR started conflicting. So we replay it.

Method
------
A PR conflicts because `main` moved and stops because someone pushed. Answering
"how long, and who fixed it" needs three things git cannot give you: which shas
were ever the PR's head, when GitHub received them, and who pushed them. A commit
is not a head (several travel in one push), its committer date is when it was
written rather than pushed, and its committer field is free text, not an account.

All three come from the **push ledger**: `pr-build` runs on `pull_request_target`
for every open, reopen, and synchronize, so one run exists per pushed head,
carrying that head's sha, the account that pushed it, and the time GitHub received
it. `main`'s first-parent history supplies the bases, from git.

An **epoch** is one head and the window it was current for. Within an epoch we
binary-search `main`'s commits -- starting from the base already in effect when
the epoch began, so a PR that is born conflicting is not missed -- for the first
one that `git merge-tree` cannot merge cleanly with that head. That commit's time,
or the epoch's start if the conflict was inherited, is the ONSET.

An **episode** spans as many epochs as it takes. A conflict is over only when a
head appears that is CLEAN against the base current at the moment it appeared;
until then, successive conflicting heads are one continuous episode, not a string
of short falsely-resolved ones.

Only such a clean successor counts as a resolution. A PR closed or merged while
still conflicting ends its episode without resolving it, and is reported as
CENSORED rather than folded into the resolution median -- otherwise abandoning a
conflicted PR would score as fixing it quickly.

A PR's own squash-merge commit is excluded from the bases it is measured against.
It conflicts with that PR's head by construction (same edits, different sha), and
leaving it in made a PR's own landing look like the event that broke it.

What this is and is not
-----------------------
For a PR the ledger covers, the head sequence, the push times, and the actors are
RECORDED, not inferred; only the conflict itself is computed, by re-running the
merge. For a PR it does not cover -- older than the workflow, or whose runs have
aged out of the API -- the tool falls back to commit dates, grouping commits
written within `--push-window` into one push. Those PRs are counted separately in
every run and their resolutions are attributed to nobody, because on that path a
commit that was never a head can invent an episode or split a real one.

Two further limits apply to both paths:

  * **Force-pushed heads that never ran a build** leave no trace anywhere. The
    ledger has what ran; a head that was pushed and superseded before its build
    started is simply absent.
  * **Monotonicity.** By default the binary search assumes a head that conflicts
    with `main` still conflicts against later `main`. Each epoch is therefore
    checked at its LAST base and reported clean if it ends clean, which drops a
    conflict that arose and cleared inside one epoch. `--exhaustive` tests every
    base instead; over this repository's whole history the two have agreed
    exactly (136 episodes, identical medians and session split), so the assumption
    is costing nothing today -- but it is an assumption, so re-check it rather than
    trust that it keeps holding.

An earlier version of this file claimed every error ran one way, making the output
a LOWER bound. That was wrong and is worth killing explicitly so nobody revives
it: on the inferred path an intermediate conflicting commit invents an episode,
which is an error in the opposite direction. Quote the ledger-covered numbers, and
treat a run with a large inferred population as correspondingly softer.

Attribution
-----------
The issue this was written for asks a specific question: are conflicts resolved
only while the author's session happens to still be alive, and never once it has
ended? A session is not visible from outside, so the proxy is the gap between a
resolving push and that same actor's previous push to that PR -- the same actor,
so one person's return is not disguised as a continuation by another's activity in
between. Every resolving push lands in one of four buckets:

    continuation   the PR's author, who had pushed to it within --session-gap
    return         the PR's author, coming back after longer than that
    other-actor    somebody else entirely -- not evidence about the author at all
    unattributed   no ledger entry for that head; counted, never guessed

If essentially every resolution is a continuation and returns are vanishingly
rare, the problem is session lifetime, not motivation, and the remedy is a
different one. Each episode also records the measured `gap`, so checking that a
conclusion is not an artefact of one `--session-gap` is a re-read of the `--json`
output rather than a re-run of the whole replay. On this repository returns run
from 60 of 110 at a half-hour gap to 23 at eight hours: never vanishing, so
authors demonstrably do come back to conflicted PRs.

Usage
-----
    conflict_stats.py [--repo-dir DIR] [--since ISO] [--jobs N] [--exhaustive]
                      [--session-gap HOURS] [--push-window SECONDS] [--no-ledger]
                      [--json OUT]

`--repo-dir` is a scratch clone this script maintains (default a temporary
directory); it fetches `main` and `refs/pull/*/head`, which for this repository is
a couple of seconds and a few megabytes. `--since` limits the analysis to PRs
created on or after an ISO date. `--no-ledger` skips the push-ledger read and
infers every head from commit dates, which is faster but makes boundaries and
actors guesses throughout. `--json` also writes the per-episode rows.

Set PUSH_LEDGER_WORKFLOW if the workflow that runs on every push is not
`pr-build.yml`; a repository without such a workflow gets the inferred path.

Needs python3's standard library, `git` >= 2.38 (for `merge-tree --write-tree`),
and an authenticated `gh` CLI.
"""

import argparse
import bisect
import datetime
import json
import os
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

REPO = os.environ.get("GH_REPO", "TauCetiProject/TauCeti")
DEFAULT_SESSION_GAP_HOURS = 2.0
# The workflow that runs on every push to every PR; its runs ARE the push ledger.
PUSH_LEDGER_WORKFLOW = os.environ.get("PUSH_LEDGER_WORKFLOW", "pr-build.yml")
# GitHub caps any one workflow-run listing at this many results, whatever
# `total_count` reports; a slice that reaches it has been truncated.
LISTING_CAP = 1000
# Stop halving a capped slice below this; a span this small that still caps is
# a genuine hole rather than something more slicing can fix.
MIN_LEDGER_SLICE = 900
# Commits written within this many seconds of each other are treated as one push.
PUSH_WINDOW_SECONDS = 120


def log(msg):
    print(msg, file=sys.stderr, flush=True)


def parse_iso(text):
    if not text:
        return None
    return int(datetime.datetime.fromisoformat(
        text.replace("Z", "+00:00")).timestamp())


def human_duration(seconds):
    seconds = max(0, int(seconds))
    days, rem = divmod(seconds, 86400)
    hours, rem = divmod(rem, 3600)
    minutes = rem // 60
    if days:
        return f"{days}d {hours}h"
    if hours:
        return f"{hours}h {minutes}m"
    return f"{minutes}m"


def median(values):
    if not values:
        return None
    ordered = sorted(values)
    mid = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[mid]
    return (ordered[mid - 1] + ordered[mid]) / 2


def percentile(values, fraction):
    if not values:
        return None
    ordered = sorted(values)
    return ordered[min(len(ordered) - 1, int(fraction * len(ordered)))]


# ----- inputs -----------------------------------------------------------------

class Mirror:
    """A scratch clone carrying `main` and every PR head, for merge replay."""

    def __init__(self, path):
        self.path = path

    def git(self, *args, check=True, stdin=None):
        result = subprocess.run(["git", "-C", self.path, *args],
                                input=stdin, capture_output=True, text=True)
        if check and result.returncode != 0:
            raise RuntimeError(f"git {' '.join(args)}: {result.stderr.strip()}")
        return result

    def fetch(self):
        os.makedirs(self.path, exist_ok=True)
        if not os.path.isdir(os.path.join(self.path, ".git")):
            subprocess.run(["git", "init", "-q", self.path], check=True)
            self.git("remote", "add", "origin", f"https://github.com/{REPO}.git")
        log(f"fetching main and every PR head into {self.path}")
        # Both refspecs are FORCED (`+`) and the PR namespace is pruned. A PR head
        # that was force-pushed since the last fetch is not a fast-forward, and
        # without the `+` the whole fetch exits non-zero -- on exactly the PRs whose
        # force-pushes this script exists to reason about.
        self.git("fetch", "-q", "--no-tags", "--prune", "origin",
                 "+refs/heads/main:refs/remotes/origin/main",
                 "+refs/pull/*/head:refs/remotes/pr/*")

    def main_history(self):
        """`main`'s first-parent commits, OLDEST first, as (sha, epoch, subject)."""
        out = self.git("log", "--format=%H %ct %s", "--first-parent",
                       "refs/remotes/origin/main").stdout
        rows = []
        for line in out.splitlines():
            parts = line.split(" ", 2)
            subject = parts[2] if len(parts) > 2 else ""
            rows.append((parts[0], int(parts[1]), subject))
        return rows[::-1]

    def pr_heads(self, number):
        """The PR's own commits as (sha, epoch), oldest first, or [] if unavailable.

        `--not refs/remotes/origin/main` drops anything already on main, so a PR
        that merged main into itself contributes only its own work, and a PR that
        was squash-merged still lists its whole branch (the squash has a different
        sha, so nothing is wrongly excluded).
        """
        result = self.git("rev-list", "--format=%H %ct", "--no-commit-header",
                          f"refs/remotes/pr/{number}", "--not",
                          "refs/remotes/origin/main", check=False)
        if result.returncode != 0:
            return []
        rows = [(line.split()[0], int(line.split()[1]))
                for line in result.stdout.splitlines() if line.strip()]
        rows.sort(key=lambda row: row[1])
        return rows

    def conflicts(self, base_sha, head_sha):
        """True iff merging `head_sha` into `base_sha` hits a content conflict.

        `merge-tree --write-tree` exits 1 for a conflicted merge and 0 for a clean
        one; anything else (a missing object, a bad ref) is unusable and raises,
        so a broken replay is never silently read as "no conflict".
        """
        result = subprocess.run(
            ["git", "-C", self.path, "merge-tree", "--write-tree", "--no-messages",
             base_sha, head_sha], capture_output=True, text=True)
        if result.returncode not in (0, 1):
            raise RuntimeError(f"merge-tree {base_sha[:8]}..{head_sha[:8]}: "
                               f"{result.stderr.strip()}")
        return result.returncode == 1


def fetch_prs(since=None):
    """Every PR, as GitHub reports it, optionally limited to `--since`."""
    fields = ("number,author,createdAt,closedAt,mergedAt,state,isDraft,title,"
              "headRefName,headRepositoryOwner")
    out = subprocess.run(
        ["gh", "pr", "list", "--repo", REPO, "--state", "all", "--limit", "5000",
         "--json", fields], capture_output=True, text=True)
    if out.returncode != 0:
        raise RuntimeError(f"gh pr list failed: {out.stderr.strip()}")
    prs = json.loads(out.stdout)
    cutoff = parse_iso(since)
    if cutoff is not None:
        prs = [p for p in prs if parse_iso(p["createdAt"]) >= cutoff]
    return prs


# ----- replay -----------------------------------------------------------------

def first_conflicting(mirror, history, lo, hi, head, exhaustive=False):
    """Index of the first base in `history[lo:hi]` that conflicts with `head`.

    None if no base in the window conflicts.

    `exhaustive` tests every base, which is correct but costs one merge per main
    commit per epoch. The default instead assumes the predicate is monotone in
    main accumulating commits, checks the LAST base, and binary-searches only if
    that conflicts. That assumption is NOT a theorem -- main can revert or
    converge on the same change and un-conflict a head -- and it fails in one
    known direction: an epoch that conflicted in the middle but ends clean is
    reported clean, so the default UNDERCOUNTS episodes and never invents one.
    Use `--exhaustive` when the count matters more than the wall clock.
    """
    if lo >= hi:
        return None
    if exhaustive:
        for index in range(lo, hi):
            if mirror.conflicts(history[index][0], head):
                return index
        return None
    if not mirror.conflicts(history[hi - 1][0], head):
        return None
    # `hi` is now known to conflict, so narrow towards the earliest that does.
    # `mid` is always < hi, so assigning hi = mid strictly shrinks the window and
    # the loop terminates; `hi = mid + 1` would not when mid == hi - 1.
    while lo < hi:
        mid = (lo + hi) // 2
        if mirror.conflicts(history[mid][0], head):
            hi = mid
        else:
            lo = mid + 1
    return lo


def ledger_index(ledger):
    """(head owner, head branch) -> its pushes, oldest first.

    A workflow run names the branch it built, not the PR, and `pull_requests[]` is
    empty for most runs here (2 of 20 sampled), so the branch is the only usable
    join. Branch names get reused, so callers must also bound by the PR's own
    lifetime -- see `pr_pushes`.
    """
    index = {}
    for sha, row in ledger.items():
        index.setdefault((row["owner"], row["branch"]), []).append((sha, row["when"]))
    for pushes in index.values():
        pushes.sort(key=lambda item: item[1])
    return index


def pr_pushes(pr, index, created, ended):
    """Every recorded push to this PR's branch during its lifetime, oldest first.

    Bounded by the PR's own window because a branch name is reused: `fix/typo` may
    belong to a dozen PRs over time, and only the pushes between this PR's opening
    and its close are its own.
    """
    owner = (pr.get("headRepositoryOwner") or {}).get("login") or ""
    branch = pr.get("headRefName") or ""
    return [(sha, when) for sha, when in index.get((owner, branch), [])
            if created <= when <= ended]


def ensure_objects(mirror, shas, batch=60):
    """Fetch any of `shas` the mirror does not have. Returns the set it now has.

    A force-pushed head is unreachable from `refs/pull/N/head`, so it is missing
    from a normal clone -- 13.5% of recorded heads here. GitHub still serves those
    objects by sha, which is what makes replaying a force-pushed head possible at
    all; without this the ledger's record of them would be discarded.
    """
    have = set()
    check = mirror.git("cat-file", "--batch-check", check=False,
                       stdin="\n".join(shas))
    for line in check.stdout.splitlines():
        parts = line.split()
        if len(parts) >= 2 and parts[1] == "commit":
            have.add(parts[0])
    missing = [sha for sha in shas if sha not in have]
    if not missing:
        return have
    log(f"fetching {len(missing)} head(s) no longer reachable from any PR ref")
    for start in range(0, len(missing), batch):
        chunk = missing[start:start + batch]
        result = mirror.git("fetch", "-q", "--no-tags", "origin", *chunk, check=False)
        if result.returncode == 0:
            have.update(chunk)
        else:
            # Fetch is all-or-nothing per invocation; retry the chunk one at a time
            # so a single unavailable object does not discard fifty good ones.
            for sha in chunk:
                if mirror.git("fetch", "-q", "--no-tags", "origin", sha,
                              check=False).returncode == 0:
                    have.add(sha)
    return have


def pr_epochs(mirror, pr, index, push_window, available):
    """The heads this PR has had, as [(sha, epoch)], plus actors and provenance.

    Provenance is reported per PR because it decides how much the row is worth:

      "recorded"  every push the ledger holds for this PR is replayable. Head
                  sequence, times, and actors are records, not inferences.
      "partial"   some recorded heads could not be fetched, so episodes may be
                  truncated. Distinguished from "recorded" deliberately: treating
                  one matching head as full coverage silently dropped the rest.
      "inferred"  no ledger coverage at all (a PR older than the workflow, or
                  whose runs aged out). Heads come from commit dates, grouped by
                  `push_window`; boundaries are guesses and actors are unknown.
    """
    number = pr["number"]
    recorded = pr.get("_pushes") or []
    if recorded:
        epochs = [(sha, when) for sha, when in recorded if sha in available]
        if epochs:
            actors = {sha: (pr["_ledger"][sha]["actor"] or "") for sha, _ in epochs}
            return epochs, actors, ("recorded" if len(epochs) == len(recorded)
                                    else "partial")
    heads = mirror.pr_heads(number)
    if not heads:
        return [], {}, "skipped"
    epochs = []
    for sha, when in heads:
        if epochs and when - epochs[-1][1] <= push_window:
            epochs[-1] = (sha, when)
        else:
            epochs.append((sha, when))
    return epochs, {}, "inferred"


def analyse_pr(mirror, history, history_times, pr, now, session_gap, exhaustive=False,
               push_window=PUSH_WINDOW_SECONDS, index=None, available=None):
    """Conflict episodes for one PR, its epochs, its actors, and how it was handled.

    `handling` is "pushed" or "inferred" per `pr_epochs`, or "skipped" when the PR
    has no commits of its own to replay -- an unfetchable head, or a merge strategy
    that put the branch commits verbatim on main. Each is counted and reported
    rather than quietly folded into "no conflict", which would flatter the result.
    """
    number = pr["number"]
    epochs, actors, handling = pr_epochs(mirror, pr, index or {}, push_window,
                                         available or set())
    if not epochs:
        return [], handling, [], {}

    # A branch's commits routinely predate the PR that proposes them, and a PR
    # cannot conflict before it exists. Clamp every epoch to the PR's creation, or
    # a commit authored a week earlier would date a "conflict" to before the PR
    # was opened and inflate its duration.
    created = parse_iso(pr.get("createdAt")) or epochs[0][1]
    ended = parse_iso(pr["mergedAt"]) or parse_iso(pr["closedAt"]) or now
    author = (pr.get("author") or {}).get("login") or ""
    # A PR's OWN squash commit is not a base it was ever measured against, and it
    # conflicts with the PR's head by construction (same edits, different sha). Left
    # in, it made the merge itself look like the thing that caused the conflict:
    # five of six sampled `merged` episodes dated their onset to the PR's own
    # landing commit. Everything from that commit onwards is out of range.
    landed = own_merge_index(history, number)
    out = []
    # An EPISODE spans as many epochs as it takes: a conflict is over only when a
    # head appears that is clean against the base current at the moment it
    # appeared. Calling every following head a resolution would fragment one
    # continuous conflict into a string of falsely resolved episodes.
    open_onset = None
    for index, (head, raw_start) in enumerate(epochs):
        start = max(raw_start, created)
        following = epochs[index + 1][1] if index + 1 < len(epochs) else ended
        if following <= start:
            continue
        # Start from the base IN EFFECT at `start`, not the first one after it: a
        # PR can be born conflicting, and a head that never sees a new main commit
        # at all still has a base to conflict with. `hi` is widened to keep that
        # one base in range even when the window contains no later commit.
        lo = base_index_at(history_times, start)
        hi = max(bisect.bisect_left(history_times, following), lo + 1)
        hi = min(hi, landed) if landed is not None else hi
        if hi <= lo:
            continue
        found = first_conflicting(mirror, history, lo, hi, head, exhaustive)
        # A conflict inherited from before this epoch began dates to the epoch's
        # start (the push, or the PR opening), never to the older main commit.
        onset = None if found is None else max(history_times[found], start)

        if open_onset is not None:
            if onset is not None and onset <= start:
                continue        # this head arrived already conflicting: same episode
            # It arrived clean, so the push that created it is the resolution.
            out.append(episode(number, author, open_onset, start, "push", index))
            open_onset = None
        if open_onset is None and onset is not None:
            open_onset = onset

    if open_onset is not None:
        if pr["mergedAt"]:
            outcome = "merged"
        elif pr["closedAt"]:
            outcome = "closed"
        else:
            outcome = "still-open"
        out.append(episode(number, author, open_onset,
                           ended if outcome != "still-open" else now, outcome, None))
    attribute(out, epochs, actors, author, session_gap)
    return out, handling, epochs, actors


def base_index_at(history_times, when):
    """Index of the last main commit at or before `when` (0 if `when` predates main)."""
    return max(0, bisect.bisect_right(history_times, when) - 1)


def own_merge_index(history, number):
    """Index of the commit where PR `number` itself landed on main, or None.

    Squash-merges here carry `(#N)` at the end of the subject, which is the only
    durable link from a main commit back to the PR it came from.
    """
    suffix = f"(#{number})"
    for index, (_, _, subject) in enumerate(history):
        if subject.rstrip().endswith(suffix):
            return index
    return None


def episode(number, author, onset, resolved, outcome, resolver_epoch):
    """One conflict episode. `resolver_epoch` indexes the push that ended it (None
    when nothing did); `resolver`/`session` are filled in by `attribute`."""
    return {
        "pr": number,
        "author": author,
        "onset": onset,
        "resolved": resolved,
        "seconds": max(0, resolved - onset),
        "outcome": "push" if resolver_epoch is not None else outcome,
        "resolver_epoch": resolver_epoch,
        "resolver": None,
        "session": None,
        "gap": None,
    }


# How a resolving push relates to whoever made it.
CONTINUATION = "continuation"   # the same actor had pushed to this PR moments before
RETURN = "return"               # the same actor came back after a gap
OTHER_ACTOR = "other-actor"     # someone other than the PR's author pushed the fix
UNATTRIBUTED = "unattributed"   # GitHub could not name the actor


def cached_ledger(path, start, end):
    """`push_ledger`, memoised on disk when `path` is given.

    Reading the ledger costs a hundred-odd API requests and a few minutes, which
    is fine once and intolerable when sweeping `--session-gap` over five values to
    check a conclusion is not an artefact of one threshold. The ledger is
    append-only history, so a cache of it does not go stale in any way that
    matters; delete the file to refresh.
    """
    if path and os.path.exists(path):
        try:
            with open(path) as handle:
                rows = json.load(handle)
            log(f"push ledger: {len(rows)} pushed heads from {path}")
            return rows
        except (OSError, ValueError, TypeError) as exc:
            log(f"push ledger cache {path} unusable ({exc}); re-reading")
    ledger = push_ledger(start, end)
    if path:
        try:
            with open(path, "w") as handle:
                json.dump(ledger, handle)
        except OSError as exc:
            log(f"could not write the ledger cache {path}: {exc}")
    return ledger


def push_ledger(start, end):
    """{head sha: (actor login, push epoch)} for every push to every PR.

    THE authoritative record of head transitions, and the thing that makes the
    session question answerable at all. `pr-build` runs on `pull_request_target`
    for every open, reopen, and synchronize, so one run exists per pushed head,
    carrying the sha that was pushed, the account that pushed it, and the time
    GitHub received it. Nothing in git can supply any of those three: a commit is
    not a head, its committer date is when it was written rather than pushed, and
    its committer identity is a free-text string, not an account.

    Read in date slices, halving any slice that reaches the API's 1000-result
    listing cap until it fits, because a capped listing is silently truncated and
    a hole in the ledger degrades attribution without saying so. A single day that
    still caps is reported as a genuine hole.
    """
    ledger = {}
    pending = [(start, end)]
    while pending:
        low, high = pending.pop()
        # Full timestamps, not dates: `created=2026-08-01..2026-08-02` is an
        # INCLUSIVE two-day span, so a date-only slice can never narrow below two
        # days and a busy repository caps out forever.
        span = (f"{datetime.datetime.fromtimestamp(low, datetime.timezone.utc):%Y-%m-%dT%H:%M:%SZ}"
                f"..{datetime.datetime.fromtimestamp(high, datetime.timezone.utc):%Y-%m-%dT%H:%M:%SZ}")
        out = subprocess.run(
            ["gh", "api", "--paginate",
             f"/repos/{REPO}/actions/workflows/{PUSH_LEDGER_WORKFLOW}/runs"
             f"?per_page=100&event=pull_request_target&created={span}",
             "--jq", '.workflow_runs[] | "\\(.head_sha) \\(.actor.login // '
                     '.triggering_actor.login // "-") \\(.created_at) '
                     '\\(.head_repository.owner.login // "-") \\(.head_branch // "-")"'],
            capture_output=True, text=True)
        if out.returncode != 0:
            log(f"push ledger: {span} unavailable ({out.stderr.strip()}); "
                f"those pushes stay unattributed")
            continue
        rows = [line.split(" ") for line in out.stdout.splitlines() if line.strip()]
        # The listing caps at 1000 no matter what `total_count` says, so a slice
        # that reaches it is TRUNCATED and must be halved and re-read rather than
        # accepted. A single day that still caps is a genuine hole; say so.
        if len(rows) >= LISTING_CAP and high - low > MIN_LEDGER_SLICE:
            middle = low + (high - low) // 2
            pending.extend([(low, middle), (middle, high)])
            continue
        if len(rows) >= LISTING_CAP:
            log(f"push ledger: {span} caps out at its smallest slice; it is incomplete")
        for parts in rows:
            if len(parts) != 5:
                continue
            sha, actor, when = parts[0], parts[1], parse_iso(parts[2])
            owner, branch = parts[3], parts[4]
            # A re-run reuses the sha; the EARLIEST run is the one the push caused.
            if when is not None and (sha not in ledger or when < ledger[sha]["when"]):
                ledger[sha] = {"actor": actor, "when": when,
                               "owner": owner, "branch": branch}
    log(f"push ledger: {len(ledger)} pushed heads")
    return ledger


def attribute(episodes, epochs, actors, pr_author, session_gap):
    """Name the actor behind each resolving push and classify the session.

    The question this tool exists to answer is about an AUTHOR's behaviour, so a
    resolution can only count as "they came back" once we know who pushed it and
    that they are the PR's author. Git cannot say: it records a committer string,
    not a GitHub account, and a maintainer or bot pushing a fix would otherwise be
    silently credited to the author.

    The gap is measured against that same actor's previous push to the PR, not
    against whoever pushed last, so one person's return is not disguised as a
    continuation by somebody else's activity in between.
    """
    for row in episodes:
        index = row.get("resolver_epoch")
        if index is None:
            continue
        sha, when = epochs[index][0], epochs[index][1]
        actor = actors.get(sha) or ""
        row["resolver"] = actor or None
        if not actor:
            row["session"] = UNATTRIBUTED
        elif actor != pr_author:
            row["session"] = OTHER_ACTOR
        else:
            previous = next((epochs[j][1] for j in range(index - 1, -1, -1)
                             if actors.get(epochs[j][0]) == actor), None)
            # Record the measured gap, not just the verdict it produced. Checking
            # that a conclusion is not an artefact of one --session-gap then costs
            # a re-read of the JSON rather than a re-run of the whole replay.
            row["gap"] = None if previous is None else when - previous
            row["session"] = (CONTINUATION if previous is not None
                              and (when - previous) <= session_gap else RETURN)
    return episodes


def replay(mirror, prs, jobs, session_gap, now, exhaustive=False,
           push_window=PUSH_WINDOW_SECONDS, ledger=None):
    history = mirror.main_history()
    history_times = [when for _, when, _ in history]
    ledger = ledger or {}
    index = ledger_index(ledger)

    # Resolve each PR's recorded pushes first, then fetch in ONE pass every head
    # object the mirror is missing. Doing it per PR would mean thousands of tiny
    # fetches; doing it not at all would discard every force-pushed head.
    wanted = []
    for pr in prs:
        created = parse_iso(pr.get("createdAt")) or 0
        ended = parse_iso(pr["mergedAt"]) or parse_iso(pr["closedAt"]) or now
        pushes = pr_pushes(pr, index, created, ended)
        pr["_pushes"], pr["_ledger"] = pushes, ledger
        wanted.extend(sha for sha, _ in pushes)
    available = ensure_objects(mirror, sorted(set(wanted))) if wanted else set()

    log(f"main has {len(history)} commits; replaying {len(prs)} PR(s) on {jobs} threads"
        + (" (exhaustive)" if exhaustive else ""))

    def one(pr):
        try:
            return analyse_pr(mirror, history, history_times, pr, now, session_gap,
                              exhaustive, push_window, index, available)
        except Exception as exc:
            log(f"PR #{pr['number']}: replay failed ({exc}); skipping")
            return [], "skipped", [], {}

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        results = list(pool.map(one, prs))

    episodes = [row for rows, _, _, _ in results for row in rows]
    handled = {}
    for _, handling, _, _ in results:
        if handling:
            handled[handling] = handled.get(handling, 0) + 1
    return episodes, handled


# ----- report -----------------------------------------------------------------

def summarise(episodes, handled, total_prs):
    lines = []
    conflicted_prs = {e["pr"] for e in episodes}
    lines.append(f"{len(episodes)} conflict episode(s) across {len(conflicted_prs)} "
                 f"of {total_prs} PR(s)")
    lines.append(
        f"provenance: {handled.get('recorded', 0)} PR(s) fully recorded in the push ledger, "
        f"{handled.get('partial', 0)} partially (some recorded heads unfetchable), "
        f"{handled.get('inferred', 0)} inferred from commit dates (boundaries and actors "
        f"are guesses there), {handled.get('skipped', 0)} with no replayable commits")

    # ONLY a push that made the branch merge again is a resolution. Closing a PR
    # that is still conflicting ends the episode without resolving anything, and
    # counting it as a fast resolution would reward abandonment; it is reported
    # separately as censored. `merged` is likewise not a push-resolution.
    resolved = [e for e in episodes if e["outcome"] == "push"]
    censored = [e for e in episodes if e["outcome"] in ("closed", "merged")]
    if resolved:
        durations = [e["seconds"] for e in resolved]
        lines.append(f"time to resolution: median {human_duration(median(durations))}, "
                     f"p90 {human_duration(percentile(durations, 0.9))}, "
                     f"max {human_duration(max(durations))}")
        over_24h = sum(1 for d in durations if d > 86400)
        lines.append(f"  {over_24h}/{len(durations)} took over 24h")
    if censored:
        lines.append(f"{len(censored)} episode(s) ended without a resolving push (the PR was "
                     f"closed or merged while still conflicting); censored, not in the median")

    by_outcome = {}
    for e in episodes:
        by_outcome.setdefault(e["outcome"], []).append(e)
    for outcome in sorted(by_outcome):
        rows = by_outcome[outcome]
        durations = [e["seconds"] for e in rows]
        lines.append(f"  outcome {outcome}: {len(rows)}, "
                     f"median {human_duration(median(durations))}")

    pushes = [e for e in episodes if e["outcome"] == "push"]
    if pushes:
        buckets = {}
        for row in pushes:
            buckets.setdefault(row["session"], []).append(row)
        lines.append(f"resolved by a push: {len(pushes)}")
        labels = [
            (CONTINUATION, "the PR's author, already pushing to it"),
            (RETURN, "the PR's author, returning after a gap"),
            (OTHER_ACTOR, "someone other than the PR's author"),
            (UNATTRIBUTED, "an actor GitHub could not name"),
        ]
        for key, description in labels:
            rows = buckets.get(key) or []
            if not rows:
                continue
            lines.append(f"  {len(rows):3} by {description}, median "
                         f"{human_duration(median([e['seconds'] for e in rows]))}")

    by_author = {}
    for e in episodes:
        by_author.setdefault(e["author"], []).append(e)
    lines.append("per author:")
    for author in sorted(by_author, key=lambda a: -len(by_author[a])):
        rows = by_author[author]
        done = [e["seconds"] for e in rows if e["outcome"] == "push"]
        live = [e for e in rows if e["outcome"] == "still-open"]
        detail = f"{len(rows)} episode(s)"
        if done:
            detail += f", median {human_duration(median(done))}"
        if live:
            detail += (f", {len(live)} still conflicting "
                       f"(oldest {human_duration(max(e['seconds'] for e in live))})")
        lines.append(f"  {author}: {detail}")
    return lines


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--repo-dir", default=None,
                        help="scratch clone to fetch into (default: a temp dir)")
    parser.add_argument("--since", default=None,
                        help="only PRs created on or after this ISO date")
    parser.add_argument("--jobs", type=int, default=min(16, (os.cpu_count() or 4)),
                        help="parallel merge replays")
    parser.add_argument("--session-gap", type=float, default=DEFAULT_SESSION_GAP_HOURS,
                        help="hours after which a resolving push counts as a return, "
                             "not a continuation of the author's current session")
    parser.add_argument("--push-window", type=int, default=PUSH_WINDOW_SECONDS,
                        help="seconds within which consecutive commits are treated as one "
                             "push (0 to treat every commit as its own head)")
    parser.add_argument("--ledger-cache", default=None,
                        help="read/write the push ledger here, so repeated runs (a "
                             "sensitivity sweep) do not re-read it from the API")
    parser.add_argument("--no-ledger", action="store_true",
                        help="skip the push ledger and infer heads from commit dates "
                             "(faster, but boundaries and actors become guesses)")
    parser.add_argument("--exhaustive", action="store_true",
                        help="test every base instead of binary-searching; slower, but "
                             "does not assume a conflict persists as main accumulates")
    parser.add_argument("--json", dest="json_out", default=None,
                        help="also write the per-episode rows here")
    args = parser.parse_args(argv)

    with tempfile.TemporaryDirectory() as scratch:
        mirror = Mirror(args.repo_dir or os.path.join(scratch, "mirror"))
        mirror.fetch()
        prs = fetch_prs(args.since)
        now = int(datetime.datetime.now(datetime.timezone.utc).timestamp())
        ledger = {} if args.no_ledger else cached_ledger(
            args.ledger_cache,
            min((parse_iso(p["createdAt"]) for p in prs), default=now), now + 86400)
        episodes, handled = replay(
            mirror, prs, args.jobs, int(args.session_gap * 3600), now,
            args.exhaustive, args.push_window, ledger)

    if args.json_out:
        with open(args.json_out, "w") as handle:
            json.dump(episodes, handle, indent=2)
        log(f"wrote {len(episodes)} episode(s) to {args.json_out}")
    for line in summarise(episodes, handled, len(prs)):
        print(line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
