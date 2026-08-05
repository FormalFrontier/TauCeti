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
binary-search `main`'s commits for the first one that `git merge-tree` cannot
merge cleanly with that head; its commit time is the conflict's ONSET. The epoch
ends when the author pushes again (a resolution, since the next epoch's head is
measured afresh) or when the PR merges or closes.

Two honest limitations, both reported rather than hidden:

  * **Rewritten history.** Force-pushed heads are gone from the server, so a PR
    whose commits all share one timestamp has no measurable pre-rebase window. We
    count those PRs and say so; they can only make the reported medians *better*
    than reality, never worse.
  * **Monotonicity.** The binary search assumes that once a head conflicts with
    `main`, later `main` commits still conflict. That is near-universally true
    (main only accumulates) but not a theorem, so each epoch is first checked at
    its LAST base: an epoch that is clean at the end is reported as clean.

Attribution
-----------
The issue this was written for asks a specific question: are conflicts resolved
only while the author's session happens to still be alive, and never once it has
ended? A session is not visible from outside, so the proxy is the gap between the
resolving push and the PR's previous push. A resolution that arrives within
`--session-gap` hours of the author's last push to that PR is a CONTINUATION (the
author was already there); anything later is a RETURN (the author came back to a
PR they had left). If essentially every resolution is a continuation and returns
are vanishingly rare, the problem is session lifetime, not motivation, and the
remedy is a different one.

Usage
-----
    conflict_stats.py [--repo-dir DIR] [--since ISO] [--jobs N]
                      [--session-gap HOURS] [--json OUT]

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
        self.git("fetch", "-q", "--no-tags", "origin",
                 "refs/heads/main:refs/remotes/origin/main",
                 "refs/pull/*/head:refs/remotes/pr/*")

    def main_history(self):
        """`main`'s first-parent commits, OLDEST first, as (sha, epoch)."""
        out = self.git("log", "--format=%H %ct", "--first-parent",
                       "refs/remotes/origin/main").stdout
        rows = [(line.split()[0], int(line.split()[1])) for line in out.splitlines()]
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

def first_conflicting(mirror, history, lo, hi, head):
    """Index of the first base in `history[lo:hi]` that conflicts with `head`.

    None if the epoch never conflicts. The LAST base is checked first, so an epoch
    that ends clean is reported clean regardless of what happened in the middle;
    only when it ends conflicted do we binary-search for where that began.
    """
    if lo >= hi:
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


def analyse_pr(mirror, history, history_times, pr, now, session_gap):
    """Conflict episodes for one PR, plus whether its history was rewritten."""
    number = pr["number"]
    heads = mirror.pr_heads(number)
    if not heads:
        return [], False
    # Collapse commits sharing a timestamp: the head during that instant is the
    # last of them. What survives is one entry per push (or per rebase).
    epochs = []
    for sha, when in heads:
        if epochs and epochs[-1][1] == when:
            epochs[-1] = (sha, when)
        else:
            epochs.append((sha, when))
    rewritten = len(epochs) == 1 and len(heads) > 1

    ended = parse_iso(pr["mergedAt"]) or parse_iso(pr["closedAt"]) or now
    out = []
    for index, (head, start) in enumerate(epochs):
        following = epochs[index + 1][1] if index + 1 < len(epochs) else ended
        if following <= start:
            continue
        lo = bisect.bisect_left(history_times, start)
        hi = bisect.bisect_left(history_times, following)
        found = first_conflicting(mirror, history, lo, hi, head)
        if found is None:
            continue
        onset = history_times[found]
        if index + 1 < len(epochs):
            resolved, outcome = following, "push"
            previous = epochs[index - 1][1] if index else start
            continuation = (following - previous) <= session_gap
        elif pr["mergedAt"]:
            # A merge with no intervening push means the conflict cleared some
            # other way (the base absorbed it, or the merge was of an older head).
            resolved, outcome, continuation = ended, "merged", None
        elif pr["closedAt"]:
            resolved, outcome, continuation = ended, "closed", None
        else:
            resolved, outcome, continuation = now, "still-open", None
        out.append({
            "pr": number,
            "author": (pr.get("author") or {}).get("login") or "",
            "onset": onset,
            "resolved": resolved,
            "seconds": resolved - onset,
            "outcome": outcome,
            "continuation": continuation,
        })
    return out, rewritten


def replay(mirror, prs, jobs, session_gap, now):
    history = mirror.main_history()
    history_times = [when for _, when in history]
    log(f"main has {len(history)} commits; replaying {len(prs)} PR(s) on {jobs} threads")

    def one(pr):
        try:
            return analyse_pr(mirror, history, history_times, pr, now, session_gap)
        except Exception as exc:
            log(f"PR #{pr['number']}: replay failed ({exc}); skipping")
            return [], False

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        results = list(pool.map(one, prs))
    episodes = [episode for rows, _ in results for episode in rows]
    rewritten = sum(1 for _, flag in results if flag)
    return episodes, rewritten


# ----- report -----------------------------------------------------------------

def summarise(episodes, rewritten, total_prs):
    lines = []
    conflicted_prs = {e["pr"] for e in episodes}
    lines.append(f"{len(episodes)} conflict episode(s) across {len(conflicted_prs)} "
                 f"of {total_prs} PR(s)")
    lines.append(f"{rewritten} PR(s) had their history rewritten with no surviving "
                 f"earlier head; their pre-rebase conflicts are not measurable")

    closed = [e for e in episodes if e["outcome"] != "still-open"]
    if closed:
        durations = [e["seconds"] for e in closed]
        lines.append(f"time to resolution: median {human_duration(median(durations))}, "
                     f"p90 {human_duration(percentile(durations, 0.9))}, "
                     f"max {human_duration(max(durations))}")
        over_24h = sum(1 for d in durations if d > 86400)
        lines.append(f"  {over_24h}/{len(durations)} took over 24h")

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
        continued = [e for e in pushes if e["continuation"]]
        returned = [e for e in pushes if not e["continuation"]]
        lines.append(f"resolved by a push: {len(continued)} while the author was "
                     f"already working the PR, {len(returned)} on a later return")
        if continued:
            lines.append(f"  continuation: median "
                         f"{human_duration(median([e['seconds'] for e in continued]))}")
        if returned:
            lines.append(f"  return:       median "
                         f"{human_duration(median([e['seconds'] for e in returned]))}")

    by_author = {}
    for e in episodes:
        by_author.setdefault(e["author"], []).append(e)
    lines.append("per author:")
    for author in sorted(by_author, key=lambda a: -len(by_author[a])):
        rows = by_author[author]
        done = [e["seconds"] for e in rows if e["outcome"] != "still-open"]
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
    parser.add_argument("--json", dest="json_out", default=None,
                        help="also write the per-episode rows here")
    args = parser.parse_args(argv)

    with tempfile.TemporaryDirectory() as scratch:
        mirror = Mirror(args.repo_dir or os.path.join(scratch, "mirror"))
        mirror.fetch()
        prs = fetch_prs(args.since)
        now = int(datetime.datetime.now(datetime.timezone.utc).timestamp())
        episodes, rewritten = replay(
            mirror, prs, args.jobs, int(args.session_gap * 3600), now)

    if args.json_out:
        with open(args.json_out, "w") as handle:
            json.dump(episodes, handle, indent=2)
        log(f"wrote {len(episodes)} episode(s) to {args.json_out}")
    for line in summarise(episodes, rewritten, len(prs)):
        print(line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
