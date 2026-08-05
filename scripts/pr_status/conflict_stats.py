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
For a PR, `main` moving is what creates a conflict, and the author pushing is what
resolves it. Both are in git:

  * The PR's own commits (`merge-base..head`, minus anything already in `main`)
    give the sequence of heads the branch has had, timestamped by committer date.
    A rebase rewrites those dates to the moment of the rebase, which is exactly
    the event we want to see.
  * `main`'s first-parent history gives every base the PR was ever measured
    against, timestamped the same way.

An **epoch** is one head and the window it was current for. Within an epoch we
binary-search `main`'s commits -- starting from the base already in effect when
the epoch began, so a PR that is born conflicting is not missed -- for the first
one that `git merge-tree` cannot merge cleanly with that head. That commit's time,
or the epoch's start if the conflict was inherited, is the ONSET.

An **episode** spans as many epochs as it takes. A conflict is over only when a
head appears that is CLEAN against the base current at the moment it appeared;
until then, successive conflicting heads are one continuous episode. This matters
because several commits pushed together look like several heads here, none of
which was ever the PR's head: treating every following commit as a resolution
would shred one long conflict into a string of short, falsely-resolved ones.

Only such a clean successor counts as a resolution. A PR closed or merged while
still conflicting ends its episode without resolving it, and is reported as
CENSORED rather than folded into the resolution median -- otherwise abandoning a
conflicted PR would score as fixing it quickly.

A PR's own squash-merge commit is excluded from the bases it is measured against.
It conflicts with that PR's head by construction (same edits, different sha), and
leaving it in made a PR's own landing look like the event that broke it.

What this is and is not
-----------------------
This is a RECONSTRUCTION, not a log. GitHub keeps no record of when a PR started
conflicting, so there is nothing to read; commits are the only durable trace of a
branch's history, and they are an imperfect proxy for it. Read the numbers with
these limits in mind, all of which are reported rather than hidden:

  * **Commit time is not push time, and a commit is not a head.** This is the
    deepest limitation and it cuts BOTH ways, so be careful with it. Commits
    pushed together were never heads individually: an intermediate commit that
    conflicts, while the tip actually pushed is clean, INVENTS an episode; an
    intermediate commit that is clean can SPLIT a real one. Grouping commits
    written within `--push-window` (default 120s) into one push removes the common
    case, and coalescing across consecutive conflicting heads removes the rest of
    the splitting, but neither makes the boundaries true. Resolutions are still
    dated to a committer timestamp rather than a push.
  * **Rewritten history.** Force-pushed heads are gone from the server. A PR whose
    surviving commits all share one timestamp is flagged `rewritten` and its
    pre-rebase window is unmeasurable; a PR force-pushed down to a single commit
    cannot be distinguished from one that always had one.
  * **Monotonicity.** By default the binary search assumes a head that conflicts
    with `main` still conflicts against later `main`. Each epoch is therefore
    checked at its LAST base and reported clean if it ends clean, which drops a
    conflict that arose and cleared inside one epoch. `--exhaustive` tests every
    base instead; over this repository's whole history the two agree exactly (96
    episodes, identical medians and session split), so the assumption is currently
    costing nothing -- but it is an assumption, so re-check it rather than trust
    that it keeps holding.

An earlier version of this file claimed all of that errs one way, making the output
a LOWER bound. That was wrong, and the claim is worth killing explicitly so nobody
revives it: an intermediate conflicting commit invents an episode, which is an
error in the opposite direction. There is no global bias to lean on.

What survives is narrower, and each claim has to earn its own keep:

  * **The unresolved tail needs no reconstruction at all.** A PR that is
    conflicting right now is a fact about the present, read straight from
    GitHub -- the episodes reported here as `still-open` match its live
    `CONFLICTING` list exactly, and that count does not move when the knobs do.
    Trust that one.
  * **Resolution durations are approximate**, with error bounded by how far apart
    a push's commits are written. Across `--push-window` from 0 to 900s the median
    ran 11m to 22m here: read it as an order of magnitude ("minutes, not days"),
    never as a number.
  * **Episode counts can move in either direction**, and do: 98 at
    `--push-window 0` down to 72 at 900s. Compare runs at several values before
    believing a count.
  * **The existence of returns is robust** even though their exact number is not:
    12-15 across every push window, 8-23 across session gaps from 30m to 8h, never
    zero. That is enough to answer the question this was built for, and no more.

Attribution
-----------
The issue this was written for asks a specific question: are conflicts resolved
only while the author's session happens to still be alive, and never once it has
ended? A session is not visible from outside, so the proxy is the gap between the
resolving push and that same actor's previous push to that PR.

WHO pushed is not a question git can answer. It records a committer name and email,
which is not a GitHub account and can say anything; a maintainer or a bot pushing
the fix would be credited to the PR's author, which is exactly the claim under
test. So the actor comes from GitHub (`/pulls/N/commits`, preferring `committer`
over `author`: a rebase keeps the original author, but the committer is who put the
commit on the branch). Every resolving push lands in one of four buckets:

    continuation   the PR's author, who had pushed to it within --session-gap
    return         the PR's author, coming back after longer than that
    other-actor    somebody else entirely -- not evidence about the author at all
    unattributed   GitHub could not name the actor; counted, never guessed

If essentially every resolution is a continuation and returns are vanishingly
rare, the problem is session lifetime, not motivation, and the remedy is a
different one. A result with plentiful returns rules that out; a result with none
is inconclusive rather than proof of the session-lifetime story, because the
push-boundary error above shortens apparent gaps and so favours continuations.
Vary `--session-gap` and `--push-window` and check the split is not an artefact of
one threshold.

Usage
-----
    conflict_stats.py [--repo-dir DIR] [--since ISO] [--jobs N] [--exhaustive]
                      [--session-gap HOURS] [--push-window SECONDS] [--json OUT]

`--repo-dir` is a scratch clone this script maintains (default a temporary
directory); it fetches `main` and `refs/pull/*/head`, which for this repository is
a couple of seconds and a few megabytes. `--since` limits the analysis to PRs
created on or after an ISO date. `--json` also writes the per-episode rows.

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

    def git(self, *args, check=True):
        result = subprocess.run(["git", "-C", self.path, *args],
                                capture_output=True, text=True)
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
    fields = "number,author,createdAt,closedAt,mergedAt,state,isDraft,title"
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


def analyse_pr(mirror, history, history_times, pr, now, session_gap, exhaustive=False,
               push_window=PUSH_WINDOW_SECONDS):
    """Conflict episodes for one PR, plus how it was handled.

    The second element is "" for a fully measured PR, "rewritten" when several
    commits survive but all share one timestamp (a force-push destroyed the
    earlier heads), or "skipped" when the PR has no commits of its own to replay
    -- an unfetchable head, or a merge strategy that put the branch commits
    verbatim on main. Each is counted and reported rather than quietly folded into
    "no conflict", which would flatter the result.

    Force-push detection is a heuristic and deliberately conservative: a PR
    force-pushed down to a SINGLE commit is indistinguishable from one that always
    had one, so it reads as fully measured. Flagging every one-commit PR would
    destroy the signal to catch a case we cannot confirm.
    """
    number = pr["number"]
    heads = mirror.pr_heads(number)
    if not heads:
        return [], "skipped", []
    # Group commits into PUSHES. Commits written within `push_window` of each other
    # almost always travelled in one push, and only the LAST of them was ever the
    # branch's head -- the earlier ones were never on GitHub on their own. Treating
    # each as its own head is what lets the replay invent a short episode from an
    # intermediate commit that conflicts, or split a real one at an intermediate
    # commit that does not. Grouping does not make the boundaries true, but it
    # removes the failure mode for the common case; `--push-window 0` disables it.
    epochs = []
    for sha, when in heads:
        if epochs and when - epochs[-1][1] <= push_window:
            epochs[-1] = (sha, when)
        else:
            epochs.append((sha, when))
    # "Rewritten" is about IDENTICAL timestamps (a rebase stamps them all at once),
    # not about grouping: several commits genuinely pushed together are not a
    # rewritten history.
    handling = "rewritten" if len({when for _, when in heads}) == 1 and len(heads) > 1 else ""

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
    # appeared. Walking epoch by epoch and calling every following commit a
    # resolution would fragment one continuous conflict into a string of falsely
    # resolved episodes -- doubly so because several commits pushed together look
    # like several heads here, none of which was ever the PR's head.
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
            # It arrived clean, so the push that created it is the resolution. WHO
            # pushed it, and whether they had been working the PR, is not knowable
            # from git alone; `attribute` fills that in from GitHub afterwards.
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
    return out, handling, epochs


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
    }


# How a resolving push relates to whoever made it.
CONTINUATION = "continuation"   # the same actor had pushed to this PR moments before
RETURN = "return"               # the same actor came back after a gap
OTHER_ACTOR = "other-actor"     # someone other than the PR's author pushed the fix
UNATTRIBUTED = "unattributed"   # GitHub could not name the actor


def commit_actors(number):
    """{sha: github login} for a PR's commits, or {} if the read fails.

    Git records a committer name and email, which is NOT a GitHub identity and can
    be anything; the API resolves each commit to the account GitHub attributes it
    to. Preferring `committer` over `author` is deliberate: a rebase or a
    web-UI edit keeps the original author but the committer is who actually put
    the commit on the branch, which is the actor whose session we are asking about.
    """
    try:
        out = subprocess.run(
            ["gh", "api", "--paginate", f"/repos/{REPO}/pulls/{number}/commits?per_page=100",
             "--jq", '.[] | "\\(.sha) \\(.committer.login // .author.login // "")"'],
            capture_output=True, text=True)
        if out.returncode != 0:
            return {}
    except OSError:
        return {}
    actors = {}
    for line in out.stdout.splitlines():
        parts = line.split(" ", 1)
        if len(parts) == 2 and parts[1].strip():
            actors[parts[0]] = parts[1].strip()
    return actors


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
            row["session"] = (CONTINUATION if previous is not None
                              and (when - previous) <= session_gap else RETURN)
    return episodes


def replay(mirror, prs, jobs, session_gap, now, exhaustive=False,
           push_window=PUSH_WINDOW_SECONDS):
    history = mirror.main_history()
    history_times = [when for _, when, _ in history]
    log(f"main has {len(history)} commits; replaying {len(prs)} PR(s) on {jobs} threads"
        + (" (exhaustive)" if exhaustive else ""))

    def one(pr):
        try:
            return analyse_pr(mirror, history, history_times, pr, now, session_gap,
                              exhaustive, push_window)
        except Exception as exc:
            log(f"PR #{pr['number']}: replay failed ({exc}); skipping")
            return [], "skipped", []

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        results = list(pool.map(one, prs))

    # Phase 2: name the actor behind each resolving push. This costs one GitHub
    # read per PR, so it runs ONLY over the handful that produced an episode --
    # ~90 of ~2000 here -- rather than over the whole queue.
    needs_actors = [(pr, rows, epochs) for pr, (rows, _, epochs) in zip(prs, results)
                    if any(row.get("resolver_epoch") is not None for row in rows)]
    log(f"attributing {len(needs_actors)} PR(s) with a resolving push")

    def name_actors(item):
        pr, rows, epochs = item
        attribute(rows, epochs, commit_actors(pr["number"]),
                  (pr.get("author") or {}).get("login") or "", session_gap)

    with ThreadPoolExecutor(max_workers=min(jobs, 8)) as pool:
        list(pool.map(name_actors, needs_actors))

    episodes = [row for rows, _, _ in results for row in rows]
    unmeasured = {"rewritten": 0, "skipped": 0}
    for _, handling, _ in results:
        if handling:
            unmeasured[handling] += 1
    return episodes, unmeasured


# ----- report -----------------------------------------------------------------

def summarise(episodes, unmeasured, total_prs):
    lines = []
    conflicted_prs = {e["pr"] for e in episodes}
    lines.append(f"{len(episodes)} conflict episode(s) across {len(conflicted_prs)} "
                 f"of {total_prs} PR(s)")
    lines.append(f"{unmeasured.get('rewritten', 0)} PR(s) had their history rewritten with "
                 f"no surviving earlier head, and {unmeasured.get('skipped', 0)} had no "
                 f"replayable commits; neither group's conflicts are measurable")

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
        episodes, unmeasured = replay(
            mirror, prs, args.jobs, int(args.session_gap * 3600), now,
            args.exhaustive, args.push_window)

    if args.json_out:
        with open(args.json_out, "w") as handle:
            json.dump(episodes, handle, indent=2)
        log(f"wrote {len(episodes)} episode(s) to {args.json_out}")
    for line in summarise(episodes, unmeasured, len(prs)):
        print(line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
