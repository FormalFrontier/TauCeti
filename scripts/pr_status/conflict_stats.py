#!/usr/bin/env python3
"""Reconstruct the history of merge conflicts in the PR queue, by replaying merges.

Only the merge replay is from git. Which shas were ever a PR's head, when GitHub
received them, who pushed them, and when the PR was closed all come from GitHub --
the `pr-build` workflow's run history and the issue timeline -- because git records
none of them. An earlier version of this line said "from git alone", which was true
of the replay and false of the tool; it is worth saying so rather than leaving the
claim to be revived.

The question is "how long are conflicts lasting", and nothing here has ever
recorded it. GitHub keeps no history of `mergeable`: it reports only the current
value, and nothing in the timeline marks the moment a PR started conflicting.
There is no log to read, so the baseline the target (median conflict-to-resolution
under 24h) is measured against has to be replayed. An earlier version of this
paragraph pointed at a `conflicts.py report` reading markers "this repository now
writes"; neither that script nor those markers exists, here or anywhere, so the
claim is recorded as false rather than left to be revived.

Method
------
A PR conflicts because `main` moved and stops because someone pushed. Answering
"how long, and who fixed it" needs three things git cannot give you: which shas
were ever the PR's head, when GitHub received them, and who pushed them. A commit
is not a head (several travel in one push), its committer date is when it was
written rather than pushed, and its committer field is free text, not an account.

All three come from the **push ledger**: `pr-build` runs on `pull_request_target`
for every open, reopen, and synchronize, so one run exists per head TRANSITION --
the head the PR was opened with, and every head pushed over it -- carrying that
head's sha, the account behind it, and the time GitHub received it. Not every run
is a push: the opening run's sha reached the branch earlier and unrecorded, since
a push to a fork's branch triggers nothing here. It still dates the head, which is
what an epoch boundary is, and Attribution below says what that means for a gap
measured back to it. `main`'s first-parent history supplies the bases, from git.

An **epoch** is one head and the window it was current for. Within an epoch we
binary-search `main`'s commits -- starting from the base already in effect when
the epoch began, so a PR that is born conflicting is not missed -- for the first
one that `git merge-tree` cannot merge cleanly with that head. That commit's time,
or the epoch's start if the conflict was inherited, is the ONSET.

An **episode** spans as many epochs as it takes. A conflict ends when a head
appears that is CLEAN against the base current at the moment it appeared; until
then, successive conflicting heads are one continuous episode, not a string of
short falsely-resolved ones. It also ends, without anybody pushing, if `main`
moves to a base the UNCHANGED head merges cleanly with: that is the outcome
`main-cleared`, and it is searched for on every run rather than assumed away --
see Monotonicity below.

Only those two count as resolutions. A PR closed or merged while still
conflicting ends its episode without resolving it, and is reported as CENSORED
rather than folded into the resolution median -- otherwise abandoning a
conflicted PR would score as fixing it quickly.

A PR that is closed and REOPENED is a different matter: nothing there resolved the
conflict, so the episode continues across the closure, with the time spent closed
discounted from its duration (`closed_seconds` records how much, and `null` when
the timeline read failed, so an unknown discount is never passed off as a checked
zero) because nobody could have merged it then. It is not split into a censored
segment plus a resolved one; that would file the pre-close segment under
"abandoned while conflicting", and the closures here are mostly the review bot
pulsing a PR shut and open again for a second at a time -- #1908 fifteen times in
one afternoon.

A PR's own squash-merge commit is excluded from the bases it is measured against.
It conflicts with that PR's head by construction (same edits, different sha), and
leaving it in made a PR's own landing look like the event that broke it.

What this is and is not
-----------------------
Every run reports provenance per PR, because it decides what a row is worth:

    recorded   every push the ledger holds for this PR is replayable. The head
               sequence, the push times, and the actors are records; only the
               conflict itself is computed, by re-running the merge.
    partial    some recorded heads could not be fetched, OR the ledger read left
               a hole spanning this PR's lifetime, so heads may be missing and
               episodes truncated. Kept distinct from `recorded` on purpose: an
               API slice that fails or caps out returns fewer pushes and looks
               exactly like a quiet week, so the hole has to be carried alongside
               the data rather than inferred from it. A PR whose recorded heads
               are ALL unfetchable is partial too, falling back to commit dates
               for its heads: the ledger covered it, so calling that row
               `inferred` or `skipped` would hide a record that exists.
    inferred   no ledger coverage -- older than the workflow, or its runs aged
               out. Heads come from commit dates grouped by `--push-window`,
               boundaries are guesses, and resolutions are attributed to nobody,
               because there a commit that was never a head can invent an episode
               or split a real one.
    skipped    nothing replayable at all, and nothing recorded to have lost.

Two further limits apply to both paths:

  * **Force-pushed heads** are recorded by the ledger but unreachable from
    `refs/pull/N/head`, so their objects are fetched by sha before replaying --
    1282 of 9477 here, and ignoring them cost 36 episodes and more than half the
    author-returns. A head pushed and superseded before its build even started
    leaves no trace anywhere and is genuinely lost.
  * **Monotonicity.** By default the binary search assumes a head that conflicts
    with `main` still conflicts against later `main`. Each epoch is therefore
    checked at its LAST base and reported clean if it ends clean, which drops a
    conflict that arose and cleared inside one epoch. `--exhaustive` tests every
    base instead; run back to back over the whole history the two agree.

    The assumption is confined to finding the ONSET. Where an episode ENDS is not
    assumed: once a conflict is open, every later base in the epoch is tried in
    turn, and the first that merges cleanly with the unchanged head ends the
    episode as `main-cleared` -- `main` moved and the conflict was over with
    nobody pushing. Leaving that out was the one place the assumption reached
    past the search: `--exhaustive` carried such an episode on to the next clean
    head, and the default dropped it.

    Over this repository's history it has never happened. The same scan run over
    every epoch rather than only the conflicting ones is 41,790 merges over 9,647
    epochs, 184 of which conflict with some base -- and NO epoch has a clean base
    after a conflicting one, so every conflict here ended at a push, at a closure,
    or is still open. That is a fact about this history rather than a theorem,
    which is why the check now runs on every replay instead of being quoted from
    one scan; comparing the two modes is the weaker instrument, since a live queue
    moves between two runs.

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
resolving push and that same actor's previous appearance on that PR -- the same
actor, so one person's return is not disguised as a continuation by another's
activity in between. Every resolving push lands in one of four buckets:

    continuation   the PR's author, last seen on it within --session-gap
    return         the PR's author, coming back after longer than that
    other-actor    somebody else entirely -- not evidence about the author at all
    unattributed   no ledger entry for that head; counted, never guessed

"Last seen" is usually their previous push, and for a PR born conflicting and
fixed shortly after it is them OPENING the PR. That is still the actor acting on
the PR at that timestamp, which is the whole content of the question, and a firmer
sign of presence than a push -- whose sha may have sat on the branch for a week.
Dropping it for not being a push would leave no earlier event at all and land the
row in `return`, asserting an absence for an author who never went away; the count
of gaps measured back to an opening is reported instead, and `gap_from` carries it
per row.

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
`--ledger-cache PATH` memoises the ledger (it costs ~100 API reads), which makes
re-running against a different `--session-gap` or `--exhaustive` cheap. The file
records the span it covers, and a later run reads the time since rather than
answering from a snapshot that predates it.

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
# What a ledger read writes for a field GitHub left null. The runs are read as
# space-separated lines, which cannot carry an empty field, so the absence needs a
# stand-in -- and the stand-in has to be turned back into an absence on the way
# in, because it is not an account: compared against the PR's author it is merely
# unequal, so an unnameable pusher's fix reads as `other-actor`, a claim that
# somebody else fixed it, rather than `unattributed`.
MISSING_FIELD = "-"
# A workflow run is created a moment after the event that triggered it, so a PR's
# `opened` run lands within this of its `createdAt` -- see `opening_epoch`.
OPENING_TOLERANCE_SECONDS = 300


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
    """Every PR, as GitHub reports it, optionally limited to `--since`.

    A reopen is NOT visible here. GitHub clears `closedAt` when a PR is reopened,
    so "open, but carries a closedAt" -- which an earlier version of this file used
    as the tell -- describes no PR at all: 0 of the 1990 in this repository. Reopens
    come from the timeline instead, in `closed_intervals`, and `closedAt` is read
    only as the date a currently-closed PR closed.
    """
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

    Either way this returns the ONSET and stops. Where the conflict ENDS is
    `first_clean`'s business, and it assumes nothing.
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


def first_clean(mirror, history, lo, hi, head):
    """Index of the first base in `history[lo:hi]` that merges cleanly with `head`.

    None if every base in the window conflicts. This is how an episode can end
    without a push: `main` moves, and the head nobody has touched merges again.

    Linear on purpose, and never binary-searched. The binary search in
    `first_conflicting` is licensed by assuming that a conflict persists as main
    accumulates commits, and this function exists precisely to test that
    assumption rather than to lean on it. It runs only while a conflict is open,
    so its cost is the conflicting epochs' windows and not the whole queue's.
    """
    for index in range(lo, hi):
        if not mirror.conflicts(history[index][0], head):
            return index
    return None


def ledger_actor(actor):
    """The account behind a ledger row, or `""` when GitHub named nobody.

    Applied both on the way out of `push_ledger` and on the way in here, because a
    cache file written before this existed still holds the raw `MISSING_FIELD` and
    would sail past a normalisation done only at the point of reading the API.
    """
    return "" if not actor or actor == MISSING_FIELD else actor


def ledger_index(ledger):
    """(head owner, head branch) -> its pushes, oldest first.

    A workflow run names the branch it built, not the PR, and `pull_requests[]` is
    empty for most runs here (2 of 20 sampled), so the branch is the only usable
    join. Branch names get reused, so callers must also bound by the PR's own
    lifetime -- see `pr_pushes`.
    """
    index = {}
    for row in ledger:
        index.setdefault((row["owner"], row["branch"]), []).append(
            (row["sha"], row["when"], ledger_actor(row["actor"])))
    for key, pushes in index.items():
        pushes.sort(key=lambda item: item[1])
        # Collapse ADJACENT repeats of one sha, which are re-runs and reopens
        # rather than head transitions, keeping the earliest. A repeat separated
        # by a different head is a real return to an earlier head and is kept.
        collapsed = []
        for row in pushes:
            if collapsed and collapsed[-1][0] == row[0]:
                continue
            collapsed.append(row)
        index[key] = collapsed
    return index


def pr_pushes(pr, index, created, ended):
    """Every recorded push to this PR's branch during its lifetime, oldest first.

    Bounded by the PR's own window because a branch name is reused: `fix/typo` may
    belong to a dozen PRs over time, and only the pushes between this PR's opening
    and its close are its own.
    """
    owner = (pr.get("headRepositoryOwner") or {}).get("login") or ""
    branch = pr.get("headRefName") or ""
    return [row for row in index.get((owner, branch), [])
            if created <= row[1] <= ended]


def closed_intervals(number):
    """[(closed_at, reopened_at)] for a PR, from its timeline; None if it failed.

    A failed read is NOT an empty one. `[]` says "this PR was never closed and
    reopened, so there is nothing to discount"; a failed read says "we do not know
    whether there is", and the two produce the same duration while deserving very
    different confidence. Returning `[]` for both let a timeline outage quietly
    leave closed time in every duration with the rows still presented as ordinary.
    Callers mark the affected episodes instead -- see `replay`.

    A PR that was closed and reopened was not in the queue in between, and a
    conflict cannot be "unresolved" during a period when nobody could merge it
    anyway. The timeline is the ONLY record of that: `closedAt` is cleared on
    reopen, so a PR that was closed and reopened is indistinguishable from one that
    never closed until you read this. 33 PRs here have been reopened, all but one
    of them now closed or merged, so a pre-filter on the list fields would have
    missed essentially all of them.
    """
    out = subprocess.run(
        ["gh", "api", f"/repos/{REPO}/issues/{number}/timeline?per_page=100",
         "--paginate", "--jq",
         '.[] | select(.event == "closed" or .event == "reopened") '
         r'| "\(.event) \(.created_at)"'],
        capture_output=True, text=True)
    if out.returncode != 0:
        log(f"PR #{number}: timeline unavailable ({out.stderr.strip()}); any time it "
            f"spent closed stays in its durations, which become upper bounds")
        return None
    intervals, closed_at = [], None
    for line in out.stdout.splitlines():
        parts = line.split()
        if len(parts) != 2:
            continue
        when = parse_iso(parts[1])
        if parts[0] == "closed" and closed_at is None:
            closed_at = when
        elif parts[0] == "reopened" and closed_at is not None:
            intervals.append((closed_at, when))
            closed_at = None
    return intervals


def clip_episodes(episodes, intervals):
    """Discount the time an episode's PR spent closed, dropping any episode that
    lies entirely inside a closed interval. The discount is recorded in
    `closed_seconds`, so `seconds` is always `resolved - onset - closed_seconds`
    and the JSON never disagrees with itself about a duration.

    A closure does NOT end an episode and a reopen does not start a new one. A
    conflict is over only when a head appears that merges cleanly (see
    `analyse_pr`), and closing a PR does not make one appear: reopen it and the
    same conflict is still there. Splitting at each boundary instead -- ending the
    pre-close segment as `closed` -- would file every one of those segments under
    the outcome that means "abandoned while still conflicting", which is the very
    misclassification this function exists to avoid. It is not hypothetical: #1908
    here was closed and reopened 15 times by the review bot, in pulses lasting 1 to
    22 seconds, and #1913 and #1917 similarly. Splitting would report one conflict
    on #1908 as 16 episodes, 15 of them abandonments that never happened.
    """
    if not intervals:
        return episodes
    kept = []
    for row in episodes:
        overlap = sum(max(0, min(row["resolved"], high) - max(row["onset"], low))
                      for low, high in intervals)
        if overlap >= row["seconds"]:
            continue
        row["closed_seconds"] = overlap
        row["seconds"] = max(0, row["seconds"] - overlap)
        kept.append(row)
    return kept


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

    `actors[i]` is who pushed `epochs[i]`, POSITIONALLY: one sha can head a branch
    more than once (an A -> B -> A force-push), and the two occurrences need not
    have the same actor. Keyed by sha instead, the later occurrence overwrote the
    earlier one's actor, which both miscredited the earlier push and let
    `attribute` find a "previous push by the same actor" that was somebody else's.

    Provenance is reported per PR because it decides how much the row is worth:

      "recorded"  every push the ledger holds for this PR is replayable. Head
                  sequence, times, and actors are records, not inferences.
      "partial"   some recorded heads could not be fetched, or the ledger read
                  left a hole over this PR's lifetime, so heads may be missing and
                  episodes truncated. Distinguished from "recorded" deliberately:
                  treating one matching head as full coverage silently dropped the
                  rest, and treating a failed API slice as "no pushes then" made
                  an incomplete history indistinguishable from a complete one.
                  Losing EVERY recorded head is partial as well, not "inferred":
                  the commit-date fallback still runs, but the ledger did cover
                  this PR, and a row that says otherwise conceals the loss.
      "inferred"  no ledger coverage at all (a PR older than the workflow, or
                  whose runs aged out). Heads come from commit dates, grouped by
                  `push_window`; boundaries are guesses and actors are unknown.
      "skipped"   nothing replayable, and no recorded head lost either.
    """
    number = pr["number"]
    recorded = pr.get("_pushes") or []
    replayable = [row for row in recorded if row[0] in available]
    if replayable:
        epochs = [(sha, when) for sha, when, _ in replayable]
        actors = [actor or "" for _, _, actor in replayable]
        complete = (len(epochs) == len(recorded)
                    and pr.get("_ledger_covered", True))
        return epochs, actors, ("recorded" if complete else "partial")
    # The ledger recorded heads for this PR and not one of them can be fetched.
    # The commit-date fallback below is all that is left, but the result is not
    # `inferred` and not `skipped`: both of those say the ledger never covered
    # this PR, and saying that here would hide the loss of a record that exists.
    # Losing every recorded head is the extreme case of losing some, so it is
    # reported as `partial` -- with the heads below guessed rather than merely
    # incomplete, which is why they are attributed to nobody either way.
    lost = bool(recorded)
    heads = mirror.pr_heads(number)
    if not heads:
        return [], [], "partial" if lost else "skipped"
    epochs = []
    for sha, when in heads:
        if epochs and when - epochs[-1][1] <= push_window:
            epochs[-1] = (sha, when)
        else:
            epochs.append((sha, when))
    return epochs, [""] * len(epochs), "partial" if lost else "inferred"


# The outcome for an episode that ended without anybody pushing: `main` moved to a
# commit the unchanged head merges cleanly with, so the conflict was simply over.
# A real resolution, but not a push, so it carries no resolver and no session.
MAIN_CLEARED = "main-cleared"


def analyse_pr(mirror, history, history_times, pr, now, session_gap, exhaustive=False,
               push_window=PUSH_WINDOW_SECONDS, index=None, available=None):
    """Conflict episodes for one PR, its epochs, its actors, and how it was handled.

    `handling` is the provenance `pr_epochs` returned -- "recorded", "partial",
    "inferred", or "skipped" when the PR has no commits of its own to replay and
    the ledger holds none either (a merge strategy that put the branch commits
    verbatim on main). Each is counted and reported rather than quietly folded
    into "no conflict", which would flatter the result.
    """
    number = pr["number"]
    epochs, actors, handling = pr_epochs(mirror, pr, index or {}, push_window,
                                         available or set())
    if not epochs:
        return [], handling, [], []

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
        cursor = lo
        if open_onset is not None:
            # A head arriving mid-conflict either inherits it or ends it, and the
            # base in effect when the head appeared is what decides which.
            if mirror.conflicts(history[lo][0], head):
                cursor = lo + 1     # same episode: look for a base that clears it
            else:
                # It arrived clean, so the push that created it is the resolution.
                out.append(episode(number, author, open_onset, start, "push", index))
                open_onset = None
        # Walk the epoch's bases, alternating between the two things that can
        # happen to this one head as main moves under it: a base that breaks the
        # merge opens an episode, and a later base that merges cleanly again ends
        # one -- with nobody having pushed, which is what `main-cleared` records.
        while cursor < hi:
            if open_onset is None:
                found = first_conflicting(mirror, history, cursor, hi, head, exhaustive)
                if found is None:
                    break
                # A conflict inherited from before this epoch began dates to the
                # epoch's start (the push, or the PR opening), never to the older
                # main commit that happened to be current then.
                open_onset = max(history_times[found], start)
                cursor = found + 1
            else:
                cleared = first_clean(mirror, history, cursor, hi, head)
                if cleared is None:
                    break
                out.append(episode(number, author, open_onset,
                                   history_times[cleared], MAIN_CLEARED, None))
                open_onset = None
                cursor = cleared + 1

    if open_onset is not None:
        # CURRENT STATE decides the outcome, never `closedAt`. Reading `closedAt`
        # first labelled a reopened PR `closed`, which censors it -- so a live
        # conflict on a reopened PR would vanish from the very tail this tool
        # exists to report. `closedAt` only dates a PR that is closed now.
        if pr["mergedAt"]:
            outcome = "merged"
        elif pr.get("state") == "OPEN":
            outcome = "still-open"
        elif pr["closedAt"]:
            outcome = "closed"
        else:
            outcome = "still-open"
        out.append(episode(number, author, open_onset,
                           ended if outcome != "still-open" else now, outcome, None))
    attribute(out, epochs, actors, author, session_gap, created)
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
    """One conflict episode. `resolver_epoch` indexes the push that ended it, and
    is None when no push did -- the PR was closed or merged, it is still
    conflicting, or `main` moved and cleared it (`MAIN_CLEARED`), which is a
    resolution with nobody to credit. `resolver`/`session` are filled in by
    `attribute`, which skips exactly those rows."""
    return {
        "pr": number,
        "author": author,
        "onset": onset,
        "resolved": resolved,
        "seconds": max(0, resolved - onset),
        # Time inside [onset, resolved] the PR spent closed, which `clip_episodes`
        # takes back out of `seconds`. Recorded rather than silently subtracted, so
        # a reader of the JSON can see why the two timestamps and the duration do
        # not agree, and can put it back if they want wall-clock instead. `None`
        # means the timeline read failed and the discount is UNKNOWN, which is not
        # the same claim as this zero.
        "closed_seconds": 0,
        "outcome": "push" if resolver_epoch is not None else outcome,
        "resolver_epoch": resolver_epoch,
        "resolver": None,
        "session": None,
        "gap": None,
        # Whether `gap` was measured to a previous PUSH by that actor or to their
        # OPENING of the PR, which is presence without being a push. Recorded
        # rather than flattened, so a reader who wants only push-to-push gaps can
        # take the other rows out without re-running anything.
        "gap_from": None,
    }


# How a resolving push relates to whoever made it.
CONTINUATION = "continuation"   # the same actor had pushed to this PR moments before
RETURN = "return"               # the same actor came back after a gap
OTHER_ACTOR = "other-actor"     # someone other than the PR's author pushed the fix
UNATTRIBUTED = "unattributed"   # GitHub could not name the actor

# What the earlier event a `gap` was measured back to actually was.
GAP_FROM_PUSH = "push"          # that actor's previous push to this PR
GAP_FROM_OPENING = "opening"    # that actor opening the PR: presence, not a push


def cached_ledger(path, start, end):
    """`push_ledger` over `[start, end]`, memoised on disk and EXTENDED, not trusted.

    Reading the ledger costs a hundred-odd API requests and a few minutes, which
    is fine once and intolerable when sweeping `--session-gap` over five values to
    check a conclusion is not an artefact of one threshold.

    A cache file is a snapshot, not the ledger: it holds the runs that existed when
    it was written, so every push since is missing from it. Read back whole, it
    would report a conflict fixed an hour ago as still open -- the live tail is the
    one figure here that needs no reconstruction, and staleness is the one way to
    corrupt it. So the file records the span it actually covers, and only the part
    of `[start, end]` outside that span is read from the API and merged in. The
    watermark is when the read STARTED, never the future `end` the caller pads its
    request with: a run created after that moment cannot be in what was read, and
    recording `end` would let the next run skip real pushes.

    A file that does not say what it covers, or does not carry the coverage holes,
    is rejected rather than read as complete -- assuming coverage because a file
    failed to mention its absence is exactly the failure the holes exist to
    prevent. Delete the file to re-read the lot.
    """
    rows, holes, covered = [], [], None
    if path and os.path.exists(path):
        try:
            with open(path) as handle:
                cached = json.load(handle)
            rows = list(cached["pushes"])
            holes = [tuple(span) for span in cached["holes"]]
            covered = (cached["from"], cached["through"])
            log(f"push ledger: {len(rows)} recorded pushes and {len(holes)} "
                f"coverage hole(s) from {path}, covering "
                f"{covered[0]}..{covered[1]}")
        except (OSError, ValueError, TypeError, KeyError) as exc:
            log(f"push ledger cache {path} unusable ({exc}); re-reading")
            rows, holes, covered = [], [], None

    read_at = int(datetime.datetime.now(datetime.timezone.utc).timestamp())
    if covered is None:
        gaps = [(start, end)]
    else:
        gaps = [(low, high) for low, high in ((start, covered[0]), (covered[1], end))
                if high > low]
        if gaps:
            log(f"push ledger: reading {len(gaps)} span(s) the cache does not cover")
    for low, high in gaps:
        fresh, fresh_holes = push_ledger(low, high)
        rows.extend(fresh)
        holes.extend(fresh_holes)

    if gaps:
        # Spans read separately meet at their endpoints, and a `created=` range is
        # inclusive at both, so one run can arrive twice. Two occurrences of a sha
        # at the SAME second on the same branch are that artefact, not a transition.
        seen, distinct = set(), []
        for row in rows:
            key = (row["sha"], row["owner"], row["branch"], row["when"], row["actor"])
            if key in seen:
                continue
            seen.add(key)
            distinct.append(row)
        rows = distinct
        window = (min(start, covered[0]) if covered else start,
                  max(covered[1], min(end, read_at)) if covered else min(end, read_at))
        if path:
            try:
                with open(path, "w") as handle:
                    json.dump({"from": window[0], "through": window[1],
                               "pushes": rows, "holes": holes}, handle)
            except OSError as exc:
                log(f"could not write the ledger cache {path}: {exc}")
    return rows, holes


def push_ledger(start, end):
    """`(pushes, holes)`: every push to every PR, and the spans nobody could read.

    THE authoritative record of head transitions, and the thing that makes the
    session question answerable at all. `pr-build` runs on `pull_request_target`
    for every open, reopen, and synchronize, so one run exists per pushed head,
    carrying the sha that was pushed, the account that pushed it, and the time
    GitHub received it. Nothing in git can supply any of those three: a commit is
    not a head, its committer date is when it was written rather than pushed, and
    its committer identity is a free-text string, not an account.

    Read in date slices, halving any slice that reaches the API's 1000-result
    listing cap until it fits, because a capped listing is silently truncated and
    a hole in the ledger degrades attribution without saying so.

    A slice that fails outright, or that still caps at the smallest span worth
    halving, leaves a HOLE: pushes made in it are missing from the result with
    nothing in the result to show they are missing. Those spans are returned
    alongside the pushes so that `covered_by_ledger` can downgrade every PR alive
    during one from `recorded` to `partial`. Dropping them on the floor -- which
    an earlier version did -- reported a PR whose heads had silently gone missing
    as fully recorded, which is the one claim this tool must never make falsely.
    """
    ledger, holes = [], []
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
                f"PRs alive then are reported partial, never recorded")
            holes.append((low, high))
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
            holes.append((low, high))
        for parts in rows:
            if len(parts) != 5:
                continue
            sha, actor, when = parts[0], parts[1], parse_iso(parts[2])
            owner, branch = parts[3], parts[4]
            # A re-run reuses the sha; the EARLIEST run is the one the push caused.
            # Every occurrence is kept. Deduplicating by (owner, branch, sha)
            # discarded a head returned to later -- an A -> B -> A force-push,
            # where the second A can be the push that resolved the conflict.
            # Repeats that really are re-runs or reopens are ADJACENT in time for
            # a branch, and `ledger_index` collapses those; a repeat with another
            # head in between is a genuine transition and survives.
            if when is not None:
                # `MISSING_FIELD` is the absence of an actor, not an actor named
                # "-"; normalise it here so nothing downstream can mistake a run
                # GitHub named nobody for a run by somebody who is not the author.
                ledger.append({"sha": sha, "actor": ledger_actor(actor),
                               "when": when, "owner": owner, "branch": branch})
    log(f"push ledger: {len(ledger)} recorded pushes"
        + (f", {len(holes)} coverage hole(s)" if holes else ""))
    return ledger, holes


def covered_by_ledger(holes, created, ended):
    """Does the ledger cover a PR alive over `[created, ended]` end to end?

    A hole overlapping that window means heads may be missing from the PR's push
    list, and nothing in the list itself says so -- the pushes that survived look
    exactly like a complete record. So the answer decides `recorded` vs `partial`
    in `pr_epochs`; it cannot be recovered later.
    """
    return not any(low <= ended and created <= high for low, high in holes)


def opening_epoch(epochs, created):
    """Index of the epoch that is the PR being OPENED rather than pushed to, or None.

    `pull_request_target` fires on `opened` as well as on `synchronize`, so a
    ledger-covered PR's first entry is the run for its opening. That entry does
    date the head -- it is the moment GitHub made that sha the PR's head, which is
    exactly what an epoch boundary means -- but the sha reached the branch at some
    earlier, unrecorded moment, since pushing a branch on a fork triggers nothing
    here. So it is not a push, and `attribute` says so rather than reporting it as
    one.

    Identified by landing at the PR's creation rather than by position: if a hole
    in the ledger swallowed the opening run, the first SURVIVING entry is a real
    push, and marking it as the opening would be a second error on top of the
    first.
    """
    if created is None or not epochs:
        return None
    return 0 if epochs[0][1] <= created + OPENING_TOLERANCE_SECONDS else None


def attribute(episodes, epochs, actors, pr_author, session_gap, created=None):
    """Name the actor behind each resolving push and classify the session.

    The question this tool exists to answer is about an AUTHOR's behaviour, so a
    resolution can only count as "they came back" once we know who pushed it and
    that they are the PR's author. Git cannot say: it records a committer string,
    not a GitHub account, and a maintainer or bot pushing a fix would otherwise be
    silently credited to the author.

    The gap is measured against that same actor's previous push to the PR, not
    against whoever pushed last, so one person's return is not disguised as a
    continuation by somebody else's activity in between.

    `actors` is indexed by EPOCH, not by sha: a head returned to after a
    force-push occupies two epochs which may have two different actors, and a
    per-sha lookup collapsed them into one.

    The earlier event the gap is measured to is not always a push: for a PR that
    was born conflicting and fixed shortly after, it is the author OPENING the PR
    (see `opening_epoch`). That still answers the question the buckets ask -- was
    this actor's session alive, or had it ended and they came back -- because
    opening a PR is that actor acting on it at that timestamp, and if anything a
    firmer sign of presence than a push, whose sha may have been sitting on the
    branch for a week. Excluding it would leave no earlier event at all and file
    an author who never went away under `return`, inventing an absence to avoid
    misnaming a presence. So it counts, and `gap_from` records which it was, so
    the split can be read either way from the JSON.
    """
    opening = opening_epoch(epochs, created)
    for row in episodes:
        index = row.get("resolver_epoch")
        if index is None:
            continue
        when = epochs[index][1]
        actor = actors[index]
        row["resolver"] = actor or None
        if not actor:
            row["session"] = UNATTRIBUTED
        elif actor != pr_author:
            row["session"] = OTHER_ACTOR
        else:
            previous = next((j for j in range(index - 1, -1, -1)
                             if actors[j] == actor), None)
            # Record the measured gap, not just the verdict it produced. Checking
            # that a conclusion is not an artefact of one --session-gap then costs
            # a re-read of the JSON rather than a re-run of the whole replay.
            row["gap"] = None if previous is None else when - epochs[previous][1]
            row["gap_from"] = (None if previous is None else GAP_FROM_OPENING
                               if previous == opening else GAP_FROM_PUSH)
            row["session"] = (CONTINUATION if previous is not None
                              and (when - epochs[previous][1]) <= session_gap
                              else RETURN)
    return episodes


def replay(mirror, prs, jobs, session_gap, now, exhaustive=False,
           push_window=PUSH_WINDOW_SECONDS, ledger=None, holes=None):
    """`(episodes, handled)` for the whole queue: every conflict episode, and how
    many PRs each provenance class accounts for.

    `handled` counts "recorded", "partial", "inferred", and "skipped" (see
    `pr_epochs`) and is reported alongside the episodes, because a run whose rows
    are mostly reconstructed is worth less than one whose rows are records, and
    nothing in the rows themselves says which it is.

    Three passes, in this order because each is affordable only once the one before
    it has finished. Resolve every PR's recorded pushes and fetch, in ONE batch,
    every head object the mirror lacks -- per PR that would be thousands of tiny
    fetches, and skipping it would discard every force-pushed head. Then replay the
    merges on `jobs` threads, a PR whose replay raises being counted "skipped"
    rather than silently read as conflict-free. Then ask the PRs that produced an
    episode, and only those, for the time they spent closed.

    Each `pr` dict is annotated in place with `_pushes` and `_ledger_covered`,
    which `analyse_pr` reads; `ledger` and `holes` come from `cached_ledger`, and
    an empty `ledger` puts every PR on the inferred path.
    """
    history = mirror.main_history()
    history_times = [when for _, when, _ in history]
    ledger = ledger or []
    holes = holes or []
    index = ledger_index(ledger)

    # Resolve each PR's recorded pushes first, then fetch in ONE pass every head
    # object the mirror is missing. Doing it per PR would mean thousands of tiny
    # fetches; doing it not at all would discard every force-pushed head.
    wanted = []
    for pr in prs:
        created = parse_iso(pr.get("createdAt")) or 0
        ended = parse_iso(pr["mergedAt"]) or parse_iso(pr["closedAt"]) or now
        pushes = pr_pushes(pr, index, created, ended)
        pr["_pushes"] = pushes
        pr["_ledger_covered"] = covered_by_ledger(holes, created, ended)
        wanted.extend(row[0] for row in pushes)
    available = ensure_objects(mirror, sorted(set(wanted))) if wanted else set()

    log(f"main has {len(history)} commits; replaying {len(prs)} PR(s) on {jobs} threads"
        + (" (exhaustive)" if exhaustive else ""))

    def one(pr):
        try:
            return analyse_pr(mirror, history, history_times, pr, now, session_gap,
                              exhaustive, push_window, index, available)
        except Exception as exc:
            log(f"PR #{pr['number']}: replay failed ({exc}); skipping")
            return [], "skipped", [], []

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        results = list(pool.map(one, prs))

    # Ask every PR that produced an episode for the time it spent closed. There is
    # no cheaper pre-filter: a reopen clears `closedAt`, so nothing in the list read
    # distinguishes a PR that was closed and reopened from one that never closed,
    # and the tell an earlier version used matched 0 of 1990 PRs while 33 had in
    # fact been reopened. Conflicted PRs are a small fraction of the whole, so this
    # is a hundred-odd timeline reads rather than a couple of thousand.
    by_pr = {}
    for rows, _, _, _ in results:
        for row in rows:
            by_pr.setdefault(row["pr"], []).append(row)
    conflicted = sorted(by_pr)
    if conflicted:
        log(f"checking {len(conflicted)} conflicted PR(s) for time spent closed")
        with ThreadPoolExecutor(max_workers=min(jobs, 8)) as pool:
            for number, intervals in zip(conflicted,
                                         pool.map(closed_intervals, conflicted)):
                if intervals is None:
                    # The read failed, so whether this PR spent time closed is
                    # unknown. `closed_seconds = None` says so in the row rather
                    # than letting a discount of zero pass for a checked zero.
                    for row in by_pr[number]:
                        row["closed_seconds"] = None
                elif intervals:
                    by_pr[number] = clip_episodes(by_pr[number], intervals)

    episodes = [row for rows, _, _, _ in results for row in rows
                if row in by_pr.get(row["pr"], [])]
    handled = {}
    for _, handling, _, _ in results:
        if handling:
            handled[handling] = handled.get(handling, 0) + 1
    return episodes, handled


# ----- report -----------------------------------------------------------------

def summarise(episodes, handled, total_prs):
    """The report as a list of lines: what was measured, how well, and what it says.

    Provenance leads, because it decides what the rest is worth, and rows whose
    timeline could not be read are called out as upper bounds. The resolution
    figures then cover the episodes that were actually resolved -- a push, or
    `main` moving so the head merged again -- while a PR closed or merged while
    still conflicting is censored and counted on its own line, since folding it in
    would score abandoning a conflicted PR as fixing it quickly. The session split
    follows, which is the question this tool was written to answer; it covers the
    push rows alone, because a `main-cleared` episode has no resolver to bucket.
    """
    lines = []
    conflicted_prs = {e["pr"] for e in episodes}
    lines.append(f"{len(episodes)} conflict episode(s) across {len(conflicted_prs)} "
                 f"of {total_prs} PR(s)")
    lines.append(
        f"provenance: {handled.get('recorded', 0)} PR(s) fully recorded in the push ledger, "
        f"{handled.get('partial', 0)} partially (heads unfetchable, or a hole in the "
        f"ledger over the PR's lifetime; where every recorded head was lost the "
        f"heads fall back to commit dates), "
        f"{handled.get('inferred', 0)} inferred from commit dates (boundaries and actors "
        f"are guesses there), {handled.get('skipped', 0)} with no replayable commits")
    # A row whose timeline could not be read still carries any time its PR spent
    # closed, so its duration is an upper bound. Say how many rather than letting
    # them sit unmarked among rows that were actually checked.
    unchecked = [e for e in episodes if e.get("closed_seconds") is None]
    if unchecked:
        lines.append(f"{len(unchecked)} episode(s) whose timeline could not be read: time the "
                     f"PR spent closed is still in their duration, so those are upper bounds")

    # A conflict is resolved when the merge comes clean again: a pushed head, or
    # main moving under an untouched one. Closing a PR that is still conflicting
    # resolves nothing, and counting it as a fast resolution would reward
    # abandonment; it is reported separately as censored, and so is `merged`.
    resolved = [e for e in episodes if e["outcome"] in ("push", MAIN_CLEARED)]
    censored = [e for e in episodes if e["outcome"] in ("closed", "merged")]
    cleared = [e for e in episodes if e["outcome"] == MAIN_CLEARED]
    if resolved:
        durations = [e["seconds"] for e in resolved]
        lines.append(f"time to resolution: median {human_duration(median(durations))}, "
                     f"p90 {human_duration(percentile(durations, 0.9))}, "
                     f"max {human_duration(max(durations))}")
        over_24h = sum(1 for d in durations if d > 86400)
        lines.append(f"  {over_24h}/{len(durations)} took over 24h")
    if cleared:
        lines.append(f"{len(cleared)} of those ended with no push at all: main moved to a "
                     f"commit the unchanged head merged cleanly with")
    if censored:
        lines.append(f"{len(censored)} episode(s) ended without the merge ever coming clean "
                     f"(the PR was closed or merged while still conflicting); censored, "
                     f"not in the median")

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
        # A `pull_request_target` run fires on `opened` too, so some of those gaps
        # run back to the author opening the PR rather than to an earlier push of
        # theirs. That is still the actor present on the PR at that moment, which
        # is what the split asks, but it is not a push and the count says so.
        from_opening = sum(1 for row in pushes
                           if row.get("gap_from") == GAP_FROM_OPENING)
        if from_opening:
            lines.append(f"  ({from_opening} of those gaps were measured back to the "
                         f"author OPENING the PR, not to an earlier push of theirs)")

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
    """Run the whole thing from the command line; returns a process exit code.

    Fetches the mirror (into `--repo-dir`, or a temporary directory thrown away on
    exit), reads the PR list and the push ledger, replays, and prints the report to
    stdout with the progress log on stderr. `--json` additionally writes the
    per-episode rows, which is what a sensitivity sweep re-reads instead of
    replaying again. The ledger is read from the oldest PR's creation to a day past
    `now`, the pad covering any skew between this clock and GitHub's; what a cached
    ledger actually covers is `cached_ledger`'s business, not the pad's.
    """
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
                             "sensitivity sweep) re-read only the time since it "
                             "was written, not the whole history")
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
        ledger, holes = ([], []) if args.no_ledger else cached_ledger(
            args.ledger_cache,
            min((parse_iso(p["createdAt"]) for p in prs), default=now), now + 86400)
        episodes, handled = replay(
            mirror, prs, args.jobs, int(args.session_gap * 3600), now,
            args.exhaustive, args.push_window, ledger, holes)

    if args.json_out:
        with open(args.json_out, "w") as handle:
            json.dump(episodes, handle, indent=2)
        log(f"wrote {len(episodes)} episode(s) to {args.json_out}")
    for line in summarise(episodes, handled, len(prs)):
        print(line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
