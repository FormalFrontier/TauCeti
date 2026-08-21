#!/usr/bin/env python3
"""Audit and create Tau Ceti's Lean toolchain tags (`v4.33.0-rc2`, `v4.34.0`, ...).

Mathlib tags every Lean release, so a project on Lean v4.34.0 can check out mathlib at
`v4.34.0` and get a tree that builds. These tags do the same for Tau Ceti.

## What the tool does

`vX` is the first commit on `main` whose `lean-toolchain` is `leanprover/lean4:X`.
`--create` tags that commit once its post-merge CI has passed and its oleans are in the
Lake cache. The tool reads both from what is already recorded, without rebuilding.

Mathlib puts its `vX` tag on the commit that bumps its own `lean-toolchain` to X, and
`scripts/check-bump.sh` requires Tau Ceti's toolchain to match mathlib's at whatever it
pins. The first `main` commit on toolchain X therefore pins mathlib at or after mathlib's
`vX` tag. The pin is usually a little past it; the tag message gives it.

## What it leaves to a human

The tool tags only commits on `main`, and reports a release `main` never ran on as
`unreachable`. Two things cause that: the daily bump stepped over the release's window on
mathlib master, which for a stable release has been fifteen hours, or mathlib cut the
release on its `stable` branch, which `check-bump.sh` will not let this repository pin.

Tagging one anyway takes four steps. `v4.33.0` was done this way:

  1. Branch `releases/vX` from the last `main` commit before the bump jumped. Change
     `lean-toolchain` and `lake-manifest.json` to pin mathlib at its `vX` tag, and nothing
     else, so no source differs from that `main` commit.
  2. Build from source and run the audits and lints that commit defines. The pin moves
     forward by at least a bump's worth, so this is where it can fail.
  3. To publish the oleans, which does not happen automatically off `main`:
     `lake build --no-build -o .lake/outputs.jsonl`, `lake cache stage`, then
     `lake cache put-staged --rev <sha> --toolchain leanprover/lean4:vX`. Run that from a
     Lake at v4.34.0-rc1 or later; earlier ones lack both flags. Then fetch the published
     mapping and diff it against the staged one.
  4. Create the annotated tag, recording that the commit was constructed.

The report then shows the release as `tagged`, notes the commit was constructed, and says
whether it found a cache. `--create` does not do any of this; step 2 is a build.

Releases older than `EARLIEST_RELEASE` are out of scope, because the Lake cache does not
reach back that far.

If a tag does not match the rule, the tool reports it and changes nothing.

## Usage

    toolchain_tags.py                        # the report
    toolchain_tags.py --json                 # the same, machine-readable
    toolchain_tags.py --create v4.33.0-rc2   # create one tag
    toolchain_tags.py --create --all         # create every tag that is ready
    toolchain_tags.py --create --all --dry-run

## Environment

    GH_TOKEN / GITHUB_TOKEN   authenticates the `gh` CLI
    GH_REPO                   this repository (default TauCetiProject/TauCeti)
    LAKE_CACHE_REVISION_ENDPOINT_PUBLIC   default https://cache.taucetiproject.org/revisions

Only python3's standard library, git, and an authenticated `gh` CLI.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import math
import os
import re
import subprocess
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "pr_status"))
import zulip as zp  # noqa: E402

REPO = os.environ.get("GH_REPO", "TauCetiProject/TauCeti")
REVISIONS = os.environ.get("LAKE_CACHE_REVISION_ENDPOINT_PUBLIC",
                           "https://cache.taucetiproject.org/revisions")

# Releases older than this are out of scope: the Lake artifact cache does not reach back
# past them, so a tag could not promise a usable cache. Raise it, never lower it.
EARLIEST_RELEASE = "v4.33.0-rc1"

RELEASE_RE = re.compile(r"\Av(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?\Z")
TOOLCHAIN_PREFIX = "leanprover/lean4:"


# --- version names -----------------------------------------------------------

def parse_release(name):
    """(major, minor, patch, rc) for a Lean release name, else None.

    A final release sorts after every rc of the same version, so rc-lessness is `inf`."""
    match = RELEASE_RE.match(name or "")
    if not match:
        return None
    major, minor, patch, rc = match.groups()
    return (int(major), int(minor), int(patch), int(rc) if rc is not None else math.inf)


def release_key(name):
    return parse_release(name) or (math.inf,) * 4


def release_of_toolchain(toolchain):
    """The release a `leanprover/lean4:vX` pin names, or None for anything else: a
    nightly, a fork channel, a local build. Only releases get tags."""
    text = (toolchain or "").strip()
    if not text.startswith(TOOLCHAIN_PREFIX):
        return None
    name = text[len(TOOLCHAIN_PREFIX):]
    return name if parse_release(name) else None


# --- this repository ---------------------------------------------------------

def git(*args, check=True):
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out = subprocess.run(("git", "-C", root) + args, capture_output=True, text=True)
    if check and out.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed: {out.stderr.strip()}")
    return out.stdout.strip()


def main_ref():
    """`origin/main` when it resolves, else `main`."""
    if git("rev-parse", "--verify", "--quiet", "origin/main", check=False):
        return "origin/main"
    return "main"


def fetch_main():
    """Bring origin/main up to date before auditing.

    The wait can run for over an hour, during which main moves by roughly a hundred
    commits, and a push-triggered checkout is pinned to the pushed commit in any case. The
    report says "here is the state", so it has to read the state now rather than the state
    when the job started."""
    git("fetch", "--quiet", "origin", "main")


def eras(ref=None):
    """Every toolchain `main` has run on, oldest first: {release, toolchain, commit}.

    Only `lean-toolchain` is read, and only at the commits that change it, which is a
    handful out of thousands. `main`'s first-parent line is the sequence of states main
    was actually in; a merged PR's own commits were never states of main."""
    if git("rev-parse", "--is-shallow-repository") == "true":
        raise RuntimeError("this is a shallow clone; toolchain_tags needs full history")
    ref = ref or main_ref()
    order = git("rev-list", "--first-parent", "--reverse", ref).split()
    if not order:
        raise RuntimeError(f"no commits on {ref}")
    changed = set(git("rev-list", "--first-parent", ref, "--", "lean-toolchain").split())
    out, state = [], None
    for index, sha in enumerate(order):
        if index and sha not in changed:
            continue
        toolchain = git("show", f"{sha}:lean-toolchain").strip()
        if toolchain == state:
            continue
        state = toolchain
        release = release_of_toolchain(toolchain)
        if release:
            out.append({"release": release, "toolchain": toolchain, "commit": sha,
                        "index": index})
    return out


def mathlib_pin(sha):
    """The mathlib rev pinned at a commit, read from the local manifest."""
    text = git("show", f"{sha}:lake-manifest.json", check=False)
    if not text:
        return None
    for package in json.loads(text).get("packages", []):
        if package.get("name") == "mathlib":
            return package.get("rev")
    return None


# --- the two facts a tag promises --------------------------------------------

def gh(path, jq=None):
    cmd = ["gh", "api", path] + (["--jq", jq] if jq else [])
    out = subprocess.run(cmd, capture_output=True, text=True)
    if out.returncode != 0:
        raise RuntimeError(f"gh api {path} failed: {out.stderr.strip()}")
    return out.stdout.strip()


def gh_optional(path, jq=None):
    """`gh`, but None when the resource does not exist. A 404 is an answer; anything
    else is still an error, so an expired token cannot pass for an absent tag."""
    try:
        return gh(path, jq)
    except RuntimeError as exc:
        if "404" in str(exc):
            return None
        raise


def ci_passed(sha):
    """Whether main's post-merge CI concluded successfully on this commit.

    None when it never ran there, which is normal: ci.yml coalesces bursts, so plenty of
    main commits have no run of their own."""
    raw = gh_optional(f"repos/{REPO}/actions/workflows/ci.yml/runs?head_sha={sha}&per_page=10",
                      jq='[.workflow_runs[] | select(.status == "completed") | .conclusion]'
                         ' | .[0] // ""')
    return (raw or "").strip() or None


def cache_published(toolchain, sha):
    """Whether the Lake cache holds a revision mapping for this commit.

    Through curl, as every other cache read in this repository is. Not urllib: the read
    host answers python's default user agent with 403 while answering curl with 200, so a
    urllib probe reports every commit as uncached and the whole report becomes noise.
    Found by running the tool, not by reading it."""
    scope = toolchain.replace("/", "--").replace(":", "---")
    url = f"{REVISIONS}/{REPO}/tc/{scope}/{sha}.jsonl"
    out = subprocess.run(["curl", "-s", "-o", "/dev/null", "-w", "%{http_code}",
                          "--max-time", "30", url], capture_output=True, text=True)
    if out.returncode != 0:
        raise RuntimeError(f"could not reach the cache at {url}: {out.stderr.strip()}")
    code = out.stdout.strip()
    if code == "200":
        return True
    if code == "404":
        return False
    raise RuntimeError(f"the cache answered HTTP {code} for {url}; that is not a verdict")


def mathlib_releases():
    """Every Lean release mathlib has tagged, oldest first.

    One request, and the only thing this tool asks mathlib. It is needed because the set of
    toolchains `main` ran on is not the set of releases: a release main stepped over, or
    could never have pinned, has no era here and would otherwise be missing from a report
    whose entire job is to say which releases have no tag."""
    raw = gh("repos/leanprover-community/mathlib4/git/matching-refs/tags/v", jq=".[].ref")
    names = {ref.rsplit("/", 1)[-1] for ref in raw.splitlines()}
    return sorted((n for n in names if parse_release(n)), key=release_key)


def existing_tags():
    """{release: commit} for the release tags this repository already has."""
    raw = gh_optional(f"repos/{REPO}/git/matching-refs/tags/",
                      jq='.[] | [.ref, .object.sha, .object.type] | @tsv') or ""
    out = {}
    for line in raw.splitlines():
        ref, sha, kind = line.split("\t")
        name = ref[len("refs/tags/"):]
        if not parse_release(name):
            continue
        out[name] = gh(f"repos/{REPO}/git/tags/{sha}", jq=".object.sha") if kind == "tag" else sha
    return out


# --- the report --------------------------------------------------------------

POLICY = """\
Tau Ceti toolchain tags
=======================

`vX` is the first commit on `main` whose lean-toolchain is `leanprover/lean4:X`.

Mathlib puts its `vX` tag on the commit that bumps its own toolchain to X, and
check-bump.sh requires this repository's toolchain to match mathlib's at whatever it pins,
so such a commit pins mathlib at or after mathlib's `vX` tag. The tag message gives the pin.

A tag is created once that commit's post-merge CI has passed and its oleans are in the Lake
artifact cache, so a checkout builds without recompiling the library. The tool reads both
from what is already recorded, without rebuilding.

The tool tags only commits on main, and reports a release main never ran on as
`unreachable`: either the daily bump stepped over its window on mathlib master, or mathlib
cut it on its `stable` branch, which check-bump.sh will not let this repository pin. Tagging
one anyway takes four manual steps, including a build. v4.33.0 was done that way; the steps
are in this script's module docstring.

Releases older than %s are out of scope, because the Lake cache has no
older entries.

If a tag does not match the rule, the tool reports it and changes nothing.
""" % EARLIEST_RELEASE

STATUSES = ("tagged", "ready", "pending", "blocked", "unreachable", "out-of-scope")


def audit(ref=None):
    """One row per Lean release in scope, oldest first.

    Per RELEASE, not per era: a release main never ran on still needs an answer, and
    "not mentioned" is not an answer."""
    tags = existing_tags()
    by_release = {era["release"]: era for era in eras(ref)}
    if not by_release:
        raise RuntimeError("main has never run on a Lean release toolchain")
    oldest = min(by_release, key=release_key)
    rows = []

    for release in sorted(set(mathlib_releases()) | set(by_release), key=release_key):
        if release_key(release) < release_key(oldest):
            continue          # predates this repository entirely; not our business
        era = by_release.get(release)
        if era is None:
            rows.append(_unreachable_row(release, tags))
            continue
        sha = era["commit"]
        row = dict(era, status=None, reason=None, mathlib_rev=mathlib_pin(sha),
                   tagged_at=tags.get(release))
        if release_key(release) < release_key(EARLIEST_RELEASE):
            row["status"] = "out-of-scope"
            row["reason"] = f"predates {EARLIEST_RELEASE}, before the Lake cache existed"
            rows.append(row)
            continue
        if row["tagged_at"]:
            if row["tagged_at"] == sha:
                row["status"] = "tagged"
            else:
                row["status"] = "blocked"
                row["reason"] = (f"tagged at {row['tagged_at'][:8]}, but the rule names "
                                 f"{sha[:8]}; a published tag is never moved")
            rows.append(row)
            continue
        conclusion = ci_passed(sha)
        row["ci"] = conclusion
        if conclusion is None:
            # Not blocked: nothing is wrong, the run has not finished. ci.yml coalesces
            # bursts, so a commit can wait an hour for a run of its own.
            row["status"] = "pending"
            row["reason"] = f"post-merge CI has not concluded on {sha[:8]}"
            rows.append(row)
            continue
        if conclusion != "success":
            row["status"] = "blocked"
            row["reason"] = f"post-merge CI on {sha[:8]} concluded {conclusion}"
            rows.append(row)
            continue
        if not cache_published(era["toolchain"], sha):
            row["status"] = "blocked"
            row["reason"] = f"no Lake cache is published for {sha[:8]}"
            rows.append(row)
            continue
        row["status"] = "ready"
        rows.append(row)
    return rows


def _unreachable_row(release, tags):
    """A release main never ran on. There is no commit to tag and nothing will construct
    one, so the only useful thing the report can do is say so and why."""
    row = {"release": release, "toolchain": toolchain_for(release), "commit": None,
           "index": None, "mathlib_rev": None, "tagged_at": tags.get(release),
           "status": "unreachable",
           "reason": "main never ran on this toolchain, so there is no commit to tag"}
    if row["tagged_at"]:
        # Someone made one by hand anyway, off a main commit, which is the only way a
        # release main never ran on can have a tag at all. Saying "no tag is possible" over
        # the top of an existing tag is the report contradicting the repository.
        row["status"] = "tagged"
        row["commit"] = row["tagged_at"]
        # Whether it has a cache is a question, not an assumption. Nothing publishes for a
        # commit off main automatically, so the usual answer is no, but one can be uploaded
        # by hand and this said otherwise for as long as it took someone to notice.
        try:
            cached = cache_published(row["toolchain"], row["commit"])
        except RuntimeError:
            cached = None
        row["reason"] = "constructed by hand: main never ran on this toolchain"
        if cached is True:
            row["reason"] += ", and a Lake cache was published for it"
        elif cached is False:
            row["reason"] += ", and it has no published Lake cache, so a checkout recompiles"
        else:
            row["reason"] += "; its Lake cache could not be checked"
        return row
    if release_key(release) < release_key(EARLIEST_RELEASE):
        row["status"] = "out-of-scope"
        row["reason"] = f"predates {EARLIEST_RELEASE}, before the Lake cache existed"
    return row


def toolchain_for(release):
    return TOOLCHAIN_PREFIX + release


def state_digest(rows):
    """A stable hash of the state worth telling someone about.

    Over (release, status) only, so rewording a reason or the policy text does not read as
    a change. `pending` releases are left out entirely: a release whose CI has not finished
    is not news, and including it would post a message on every bump saying "wait", then
    another when the waiting ended. `out-of-scope` is left out because it never changes."""
    interesting = sorted((r["release"], r["status"], r.get("commit"), r.get("ci"))
                         for r in rows
                         if r["status"] not in ("pending", "out-of-scope"))
    return hashlib.sha256(repr(interesting).encode()).hexdigest()[:16]


def render(rows, include_policy=True, collapse_old=False):
    lines = [POLICY, ""] if include_policy else []
    head = f"{'release':14s} {'status':12s} {'commit':9s} {'mathlib':9s} note"
    lines += [head, "-" * max(len(head), 72)]
    if collapse_old:
        # Out-of-scope releases never change, and there are seven of them against four that
        # do. In a message posted whenever something changes, they are the whole screen and
        # none of the news.
        old = [r for r in rows if r["status"] == "out-of-scope"]
        rows = [r for r in rows if r["status"] != "out-of-scope"]
        if old:
            lines.append(f"({len(old)} releases up to {old[-1]['release']} are out of "
                         f"scope; run the report to list them)")
    for row in rows:
        lines.append(f"{row['release']:14s} {row['status']:12s} "
                     f"{(row['commit'] or '-')[:8]:9s} "
                     f"{(row['mathlib_rev'] or '-')[:8]:9s} {row['reason'] or ''}")
    ready = [r for r in rows if r["status"] == "ready"]
    lines.append("")
    if ready:
        lines += ["To create the tags that are ready:", "",
                  "    python3 scripts/toolchain_tags.py --create --all", "",
                  "or one at a time:", ""]
        lines += [f"    python3 scripts/toolchain_tags.py --create {r['release']}" for r in ready]
    else:
        lines.append("Nothing is ready to tag.")
    pending = [r for r in rows if r["status"] == "pending"]
    if pending:
        lines += ["", "Waiting on CI, nothing to do yet:", ""]
        lines += [f"    {r['release']}: {r['reason']}" for r in pending]
    blocked = [r for r in rows if r["status"] == "blocked"]
    if blocked:
        lines += ["", "Needing a human:", ""]
        lines += [f"    {r['release']}: {r['reason']}" for r in blocked]
    unreachable = [r for r in rows if r["status"] == "unreachable"]
    if unreachable:
        lines += ["", "No tag is possible for these, and none will be constructed:", ""]
        lines += [f"    {r['release']}: {r['reason']}" for r in unreachable]
        lines += ["",
                  "    Either the daily bump stepped over the release's window on mathlib",
                  "    master, which for a stable release has been as short as fifteen hours,",
                  "    or mathlib cut it on its `stable` branch, which check-bump.sh could",
                  "    never have let this repository pin at all."]
    return "\n".join(lines) + "\n"


# --- creating a tag ----------------------------------------------------------

def tag_message(row):
    pin = row["mathlib_rev"] or "unknown"
    return (f"TauCeti {row['release']}\n\n"
            f"Lean toolchain: {row['toolchain']}\n"
            f"Mathlib:        {pin}\n"
            f"Commit:         {row['commit']} (first commit on main with this toolchain)\n\n"
            f"Its post-merge CI passed and its oleans are published to the Lake artifact\n"
            f"cache, so a checkout of this tag builds without recompiling the library.\n"
            f"The mathlib pin is whatever main carried here, which is at or after mathlib's\n"
            f"own {row['release']} tag.\n")


def create_tag(row, dry_run=False):
    """Create one annotated tag. Never moves an existing one."""
    release, sha = row["release"], row["commit"]
    if row["status"] != "ready":
        raise RuntimeError(f"{release} is {row['status']}, not ready: {row['reason'] or ''}")
    if dry_run:
        print(f"would tag {release} at {sha}\n" + tag_message(row))
        return False
    now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    tagger = git("config", "user.name", check=False) or "tauceti"
    email = git("config", "user.email", check=False) or "tauceti@localhost"
    out = subprocess.run(
        ["gh", "api", "-X", "POST", f"repos/{REPO}/git/tags",
         "-f", f"tag={release}", "-f", f"message={tag_message(row)}",
         "-f", f"object={sha}", "-f", "type=commit",
         "-f", f"tagger[name]={tagger}", "-f", f"tagger[email]={email}",
         "-f", f"tagger[date]={now}", "--jq", ".sha"],
        capture_output=True, text=True)
    if out.returncode != 0:
        raise RuntimeError(f"could not create the tag object: {out.stderr.strip()}")
    obj = out.stdout.strip()
    gh_ref = subprocess.run(
        ["gh", "api", "-X", "POST", f"repos/{REPO}/git/refs",
         "-f", f"ref=refs/tags/{release}", "-f", f"sha={obj}", "--jq", ".ref"],
        capture_output=True, text=True)
    if gh_ref.returncode != 0:
        raise RuntimeError(f"could not create the tag ref: {gh_ref.stderr.strip()}")
    print(f"created {release} at {sha[:8]}")
    return True


# --- waiting, and posting to Zulip ------------------------------------------

MARKER_RE = re.compile(r"<!--toolchain-tags:v1 ([0-9a-f]{16})-->\s*\Z")


def wait_for_ci(sha, timeout_minutes=180, poll_seconds=120, sleep=None):
    """Block until main's post-merge CI concludes on `sha`. Returns its conclusion, or
    None on timeout.

    The push that changes `lean-toolchain` arrives 40 to 70 minutes before the release can
    be tagged: ci.yml coalesces bursts, so the bump waits for a run of its own, and that run
    then takes 20 to 30 minutes and publishes the cache at the end of it. Reporting at push
    time would always say "not yet", so wait for the thing being waited on."""
    sleep = sleep or time.sleep
    deadline = time.monotonic() + timeout_minutes * 60
    while True:
        conclusion = ci_passed(sha)
        if conclusion is not None:
            return conclusion
        if time.monotonic() >= deadline:
            return None
        log(f"post-merge CI has not concluded on {sha[:8]}; waiting")
        sleep(poll_seconds)


def log(message):
    print(message, flush=True)


def last_posted_digest(z, bot_id):
    """The digest carried by this account's newest message in the topic, or None.

    The previous state lives in the topic rather than in a file, so the poster keeps no
    state of its own and a wiped topic simply reposts."""
    messages = z.get_messages([
        {"operator": "channel", "operand": zp.CHANNEL},
        {"operator": "topic", "operand": zp.TOPIC},
    ])
    for message in sorted(messages, key=lambda m: m["id"], reverse=True):
        if message["sender_id"] != bot_id:
            continue
        match = MARKER_RE.search(message["content"])
        if match:
            return match.group(1)
    return None


def post_content(rows, digest):
    """The command someone would run, and what it printed."""
    body = render(rows, include_policy=False, collapse_old=True).rstrip()
    # The command shown must be the one that produced what is shown. --brief is exactly
    # this transformation, so someone can paste it and get the same thing back.
    return (f"```\npython3 scripts/toolchain_tags.py --brief\n```\n"
            f"```text\n{body}\n```\n"
            f"<!--toolchain-tags:v1 {digest}-->")


def post_if_changed(rows, dry_run=False):
    """Post the report when the state has changed since the last message. Returns True if
    a message was posted."""
    digest = state_digest(rows)
    content = post_content(rows, digest)
    if dry_run:
        print(content)
        return False

    email = (os.environ.get("ZULIP_EMAIL") or "").strip()
    api_key = (os.environ.get("ZULIP_API_KEY") or "").strip()
    site = (os.environ.get("ZULIP_SITE") or "https://leanprover.zulipchat.com").strip()
    if not (email and api_key):
        raise RuntimeError("ZULIP_EMAIL / ZULIP_API_KEY are not set")
    z = zp.Zulip(email, api_key, site)
    zp.check(z)
    previous = last_posted_digest(z, z.my_user_id())
    if previous == digest:
        log(f"state unchanged since the last post ({digest}); saying nothing")
        return False
    log(f"state changed ({previous or 'nothing posted yet'} -> {digest}); posting")
    z.send_message(content)
    return True


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Audit and create Tau Ceti's Lean toolchain tags.",
        formatter_class=argparse.RawDescriptionHelpFormatter, epilog=POLICY)
    parser.add_argument("--create", metavar="vX", nargs="?", const="",
                        help="create the tag for this release (with --all, every ready one)")
    parser.add_argument("--all", action="store_true", help="with --create, every ready release")
    parser.add_argument("--json", action="store_true", help="machine-readable report")
    parser.add_argument("--brief", action="store_true",
                        help="the report without the policy header, old releases collapsed")
    parser.add_argument("--post", action="store_true",
                        help="post the report to Zulip if the state has changed")
    parser.add_argument("--wait-for-ci", metavar="SHA",
                        help="with --post, wait for main's CI to conclude on SHA first")
    parser.add_argument("--wait-minutes", type=int, default=180,
                        help="with --wait-for-ci, how long to wait (default 180)")
    parser.add_argument("--dry-run", action="store_true",
                        help="with --create or --post, print instead of acting")
    args = parser.parse_args(argv)

    if args.wait_for_ci:
        if not re.fullmatch(r"[0-9a-f]{40}", args.wait_for_ci):
            parser.error("--wait-for-ci needs a 40-hex commit sha")
        conclusion = wait_for_ci(args.wait_for_ci, timeout_minutes=args.wait_minutes)
        if conclusion is None:
            # Exit red rather than quietly reporting nothing. The release stays `pending`,
            # which the digest ignores, so Zulip would say nothing and the run would be
            # green: a release that never got reported would look exactly like a quiet
            # night. Zulip is for "the state changed"; a red run is for "I could not do my
            # job". Re-dispatch once CI has finished.
            print(f"toolchain_tags: CI on {args.wait_for_ci[:8]} had not concluded after "
                  f"{args.wait_minutes} minutes; nothing reported", file=sys.stderr)
            return 1
        log(f"CI on {args.wait_for_ci[:8]} concluded {conclusion}")

    try:
        fetch_main()
        rows = audit()
    except RuntimeError as exc:
        print(f"toolchain_tags: {exc}", file=sys.stderr)
        return 2

    if args.post:
        try:
            post_if_changed(rows, dry_run=args.dry_run)
        except Exception as exc:
            # Includes a Zulip misconfiguration. Fail loudly: a reporter nobody can hear
            # is worse than no reporter, because the topic's silence reads as good news.
            print(f"toolchain_tags: could not post: {exc}", file=sys.stderr)
            return 1
        return 0

    if args.create is None:
        if args.json:
            print(json.dumps(rows, indent=2, sort_keys=True))
        else:
            print(render(rows, include_policy=not args.brief, collapse_old=args.brief), end="")
        return 0

    if args.all:
        wanted = [r for r in rows if r["status"] == "ready"]
        if not wanted:
            print("nothing is ready to tag")
            return 0
    else:
        if not args.create:
            parser.error("--create needs a release name, or --all")
        wanted = [r for r in rows if r["release"] == args.create]
        if not wanted:
            print(f"toolchain_tags: main never ran on {args.create}", file=sys.stderr)
            return 1
    for row in wanted:
        try:
            create_tag(row, dry_run=args.dry_run)
        except RuntimeError as exc:
            print(f"toolchain_tags: {exc}", file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
