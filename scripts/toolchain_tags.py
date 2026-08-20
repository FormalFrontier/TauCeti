#!/usr/bin/env python3
"""Audit and create Tau Ceti's Lean toolchain tags (`v4.33.0-rc2`, `v4.34.0`, ...).

Mathlib tags every Lean release, so a downstream project on Lean v4.34.0 can check out
mathlib at `v4.34.0` and get a tree that builds. This gives Tau Ceti the same thing.

## The rule, in one line

`vX` is the FIRST commit on `main` whose `lean-toolchain` is `leanprover/lean4:X`.

That is the whole policy, and it is deliberately not cleverer than that. It gives the
property you actually want for free: mathlib puts its own `vX` tag on the commit that bumps
its `lean-toolchain` to X, and `scripts/check-bump.sh` already forces Tau Ceti's toolchain
to equal mathlib's at whatever it pins. So the first `main` commit on toolchain X
necessarily pins mathlib at or after mathlib's own `vX` tag. Nothing here has to compute
that, compare pins, derive a base, or ask mathlib anything at all.

Two consequences worth stating plainly, because they are the cost of the simplicity:

  * A release `main` never ran on gets no tag. Today that is `v4.33.0`, whose window on
    mathlib master was fifteen hours and which the daily bump stepped over, and the patch
    releases `v4.32.1` and `v4.32.2`, which mathlib cut on its `stable` branch and which
    `check-bump.sh` could never have let this repository pin in the first place.
  * The mathlib pin is whatever `main` had, which is at or past mathlib's tag but rarely
    exactly it. The tag message records the pin so a reader can see how far past.

## What a tag promises

The commit is on that Lean toolchain, its post-merge CI passed, and its oleans are in the
Lake artifact cache, so a checkout builds without recompiling the library. Both of those
are checked before a tag is created; neither needs a rebuild, because `main` already did
the work and recorded it.

Releases before the Lake cache existed, everything up to and including `v4.32.0`, are
deliberately out of scope: there is no cache to promise. See `EARLIEST_RELEASE`.

## Usage

    toolchain_tags.py                     # the report
    toolchain_tags.py --json              # the same, machine-readable
    toolchain_tags.py --create v4.33.0-rc2   # create one tag
    toolchain_tags.py --create --all      # create every tag that is ready
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
import json
import math
import os
import re
import subprocess
import sys

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

`vX` is the FIRST commit on `main` whose lean-toolchain is `leanprover/lean4:X`.

That is the whole rule. Mathlib tags the commit that bumps its own toolchain to X, and
check-bump.sh forces this repository's toolchain to equal mathlib's at whatever it pins, so
such a commit necessarily pins mathlib at or after mathlib's own `vX` tag. The tag message
records the pin so a reader can see how far past it is.

A tag is created only once that commit's post-merge CI has passed and its oleans are in the
Lake artifact cache, so a checkout builds without recompiling the library. Neither needs a
rebuild: main already did the work.

A release main never ran on gets no tag, and nothing here will construct one. Releases
older than %s are out of scope: the Lake cache does not reach back that far, so a tag could
not promise a usable cache.

Tags are never moved. If one disagrees with this rule, that is a question for a human.
""" % EARLIEST_RELEASE

STATUSES = ("tagged", "ready", "blocked", "out-of-scope")


def audit(ref=None):
    """One row per toolchain main has run on, oldest first."""
    tags = existing_tags()
    rows = []
    for era in eras(ref):
        release, sha = era["release"], era["commit"]
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
        if conclusion != "success":
            row["status"] = "blocked"
            row["reason"] = (f"post-merge CI on {sha[:8]} "
                             + ("never ran" if conclusion is None else f"concluded {conclusion}"))
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


def render(rows):
    lines = [POLICY, ""]
    head = f"{'release':14s} {'status':12s} {'commit':9s} {'mathlib':9s} note"
    lines += [head, "-" * max(len(head), 72)]
    for row in rows:
        lines.append(f"{row['release']:14s} {row['status']:12s} {row['commit'][:8]:9s} "
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
    blocked = [r for r in rows if r["status"] == "blocked"]
    if blocked:
        lines += ["", "Needing a human:", ""]
        lines += [f"    {r['release']}: {r['reason']}" for r in blocked]
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


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Audit and create Tau Ceti's Lean toolchain tags.",
        formatter_class=argparse.RawDescriptionHelpFormatter, epilog=POLICY)
    parser.add_argument("--create", metavar="vX", nargs="?", const="",
                        help="create the tag for this release (with --all, every ready one)")
    parser.add_argument("--all", action="store_true", help="with --create, every ready release")
    parser.add_argument("--json", action="store_true", help="machine-readable report")
    parser.add_argument("--dry-run", action="store_true", help="with --create, print only")
    args = parser.parse_args(argv)

    try:
        rows = audit()
    except RuntimeError as exc:
        print(f"toolchain_tags: {exc}", file=sys.stderr)
        return 2

    if args.create is None:
        print(json.dumps(rows, indent=2, sort_keys=True) if args.json else render(rows), end="")
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
