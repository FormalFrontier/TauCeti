#!/usr/bin/env python3
"""Audit and materialise Tau Ceti's Lean toolchain tags (`v4.33.0`, `v4.33.0-rc2`, ...).

Mathlib tags every Lean release, so a downstream project can check out mathlib at
`v4.33.0` and get a tree that builds on Lean v4.33.0. This tool gives Tau Ceti the
same thing, and audits which releases still lack one.

## What a toolchain tag means

For every Lean release `X` that Tau Ceti's history can reach, the tag `vX` points at
the FIRST `main`-reachable commit whose `lean-toolchain` is exactly
`leanprover/lean4:X` and whose mathlib pin is at or after mathlib's own `vX` tag
commit `M`. The pin is, in order of preference:

  1. exact -- `M` itself. The commit is either already on `main`, or is a single
     commit on a `releases/vX` branch whose parent is a `main` commit and which
     changes only `lake-manifest.json` and `lean-toolchain`.
  2. inexact -- when no exact commit exists or the exact one will not compile, the
     first `main` commit on toolchain `X`. The tag message records how many mathlib
     commits past `M` the pin is.

"First" is uniform across both rungs, and for the exact rung it is forced: a run of
commits sharing a pin at the tip of `main` is open-ended, so "last" would want to
move the tag every day, while "first" is immutable the moment the run begins.

A tag is created only after a from-source build of that commit passes the audits and
lints `main` runs and its oleans have been published. Tags are never moved: this tool
never emits a recipe containing `-f`, `--force` or `tag -d`.

## Usage

    # the report, with repair instructions for every gap:
    toolchain_tags.py --audit
    toolchain_tags.py --audit --release v4.33.0
    toolchain_tags.py --audit --json          # the canonical worklist
    toolchain_tags.py --audit --strict        # exit 1 if any release is blocked

    # what the daily bump should pin instead of the last-known-good commit:
    toolchain_tags.py --next-stepping-stone

    # materialise a release commit's two pin files into a worktree:
    toolchain_tags.py --write v4.33.0 --dir .

    # the annotated tag body, and the Zulip reconciler:
    toolchain_tags.py --tag-message v4.33.0
    toolchain_tags.py --alert [--dry-run]

## Environment

    GH_TOKEN / GITHUB_TOKEN   authenticates the `gh` CLI (all upstream reads)
    GH_REPO                   this repository (default TauCetiProject/TauCeti)
    MATHLIB_REPO              default leanprover-community/mathlib4
    TOOLCHAIN_TAGS_CACHE      memo file for immutable upstream facts
                              (default .git/tauceti/toolchain-tags-cache.json)
    ZULIP_EMAIL, ZULIP_API_KEY, ZULIP_SITE, ZULIP_CHANNEL, ZULIP_TOPIC   for --alert

Only python3's standard library and an authenticated `gh` CLI. Nothing here builds,
tags or pushes: it names commits and prints instructions, and `.github/workflows/
release-tag.yml` is what verifies, publishes and tags them.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "pr_status"))
import core  # noqa: E402
import zulip as zp  # noqa: E402

# --- policy constants --------------------------------------------------------

MATHLIB = os.environ.get("MATHLIB_REPO", "leanprover-community/mathlib4")
REPO = core.REPO

# The two files a release commit may differ from its main base in, and nothing else.
PIN_FILES = ("lake-manifest.json", "lean-toolchain")

RELEASE_BRANCH_FMT = "releases/{release}"

# WHICH commit of an exact-pin run carries the tag. "first", and this is not a
# preference: a run at the tip of main is open-ended, because main keeps appending
# commits that share the pin until the next bump. Under "last" the tag would want to
# move every day and would never be idempotent. "first" is fixed the moment the run
# begins. The same rule applies to the inexact rung, where it is a choice: one uniform
# meaning for `vX` is worth more than the extra mathematics "last" would pick up.
RUN_TAG_POLICY = "first"

# How long automation gets to act on an actionable release before it is worth waking
# a human over. Measured from the mathlib tag's own commit date.
GRACE_HOURS = 48

# The workflow whose run conclusion on a target commit is the durable record of
# "this was built from source and published".
VERIFY_WORKFLOW = "release-tag.yml"

# `[^<>]` rather than `.`: a greedy `.*` would run from the FIRST marker's brace to
# the LAST one's, so a body quoting a marker would make the real payload unparseable.
# No payload this tool writes can contain an angle bracket, and `-->` contains one.
_TAG_MARKER_RE = re.compile(r"<!--tauceti-toolchain-tag:v1 (\{[^<>]*\})-->\s*\Z", re.S)

# --- version algebra (pure) --------------------------------------------------

# `v4.32.0-rc1-patch1` and `v2024` are deliberately rejected: the first is a mathlib
# patch of its own tree at an unchanged toolchain, not a Lean release, and `vX` is
# already taken by the Lean release it belongs to.
RELEASE_RE = re.compile(r"\Av(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?\Z")

TOOLCHAIN_PREFIX = "leanprover/lean4:"


def parse_release(name):
    """(major, minor, patch, rc) for a Lean release name, else None.

    A final release sorts AFTER every rc of the same version, so rc-lessness is
    `inf` rather than 0. This is the same ordering `scripts/check-bump.sh` step 4
    applies to the toolchain, and a test asserts the two agree."""
    m = RELEASE_RE.match(name or "")
    if not m:
        return None
    major, minor, patch, rc = m.groups()
    return (int(major), int(minor), int(patch), int(rc) if rc is not None else math.inf)


def is_release(name):
    return parse_release(name) is not None


def toolchain_for(release):
    return TOOLCHAIN_PREFIX + release


def release_of_toolchain(toolchain):
    """The release a `leanprover/lean4:vX` pin names, or None for anything else
    (a nightly, a fork channel, a local build)."""
    tc = (toolchain or "").strip()
    if not tc.startswith(TOOLCHAIN_PREFIX):
        return None
    name = tc[len(TOOLCHAIN_PREFIX):]
    return name if is_release(name) else None


def release_key(name):
    """Sort key that puts unparseable names last rather than raising."""
    return parse_release(name) or (math.inf, math.inf, math.inf, math.inf)


def release_lt(a, b):
    return release_key(a) < release_key(b)


# --- Tau Ceti git ------------------------------------------------------------

def git(*args, check=True):
    """Run git in the repository this script lives in. Returns stdout, stripped."""
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out = subprocess.run(("git", "-C", root) + args, capture_output=True, text=True)
    if check and out.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed: {out.stderr.strip()}")
    return out.stdout.strip()


def assert_full_history():
    """A shallow clone silently truncates the segment table, which would move every
    index and mis-derive every base. Fail loudly instead."""
    if git("rev-parse", "--is-shallow-repository") == "true":
        raise RuntimeError(
            "this is a shallow clone; toolchain_tags needs full history "
            "(actions/checkout with fetch-depth: 0)")


def main_ref():
    """`origin/main` when it resolves, else `main`: CI checkouts have the remote ref,
    a local clone on another branch may only have the local one."""
    if git("rev-parse", "--verify", "--quiet", "origin/main", check=False):
        return "origin/main"
    return "main"


def blob_at(sha, path):
    out = git("show", f"{sha}:{path}", check=False)
    return out or None


def read_pin(sha):
    """(toolchain, mathlib_rev) at a commit, from the two pin files."""
    toolchain = (blob_at(sha, "lean-toolchain") or "").strip()
    manifest = blob_at(sha, "lake-manifest.json")
    rev = None
    if manifest:
        for pkg in json.loads(manifest).get("packages", []):
            if pkg.get("name") == "mathlib":
                rev = pkg.get("rev")
    return toolchain, rev


def segments_from(order, changed, read):
    """Fill-forward the (toolchain, pin) state along `order`, reading only at index 0
    and at commits in `changed`.

    Reading every commit is what makes the naive version unusable: 3300 commits is
    two `git show` calls each, and only 47 of them touch a pin file. A commit in
    `changed` whose state is unchanged extends the current segment rather than
    splitting it, so segment boundaries mean "the pin actually moved"."""
    segments = []
    state = None
    for index, sha in enumerate(order):
        if index == 0 or sha in changed:
            new = read(sha)
            if new != state:
                state = new
                segments.append({
                    "first_index": index, "last_index": index,
                    "first_sha": sha, "last_sha": sha,
                    "toolchain": state[0], "mathlib_rev": state[1],
                })
                continue
        if not segments:
            raise RuntimeError("segment walk started without a pin state")
        segments[-1]["last_index"] = index
        segments[-1]["last_sha"] = sha
    return segments


def compute_segments(ref=None):
    """The (toolchain, pin) segments of main, oldest first, along the first-parent
    line. First-parent is the right notion of "states main passed through": a merged
    PR's own commits are not states main was ever in."""
    assert_full_history()
    ref = ref or main_ref()
    order = git("rev-list", "--first-parent", "--reverse", ref).split()
    if not order:
        raise RuntimeError(f"no commits on {ref}")
    changed = set(git("rev-list", "--first-parent", ref, "--", *PIN_FILES).split())
    return segments_from(order, changed, read_pin)


def assert_monotone(segments):
    """Segment toolchains never move backward. Base derivation binary-searches on the
    assumption that main's pin advances monotonically; if that ever stops being true
    the search would silently return a wrong base, so fail closed here instead."""
    for earlier, later in zip(segments, segments[1:]):
        a, b = earlier["toolchain"], later["toolchain"]
        if a == b:
            continue
        ra, rb = release_of_toolchain(a), release_of_toolchain(b)
        if ra is None or rb is None:
            continue  # a nightly or fork channel: unordered, not evidence of a move back
        if release_lt(rb, ra):
            raise RuntimeError(
                f"main's toolchain moved backward: {a} at {earlier['first_sha'][:8]} "
                f"then {b} at {later['first_sha'][:8]}")


# --- upstream facts, through the gh CLI --------------------------------------

def _gh(path, jq=None, paginate=False):
    return core.gh_api(path, jq=jq, paginate=paginate)


def _gh_optional(path, jq=None):
    """`_gh`, but None when the resource does not exist. A 404 is an answer here
    (no such tag, no such branch); anything else is still an error, so an expired
    token cannot be mistaken for an absent tag."""
    try:
        return _gh(path, jq=jq)
    except RuntimeError as exc:
        if "404" in str(exc):
            return None
        raise


class Cache:
    """A best-effort memo for IMMUTABLE upstream facts, keyed by a tuple.

    Lives inside `.git/`, so it can never be committed and needs no ignore entry.
    Every failure mode (missing, corrupt, unwritable) degrades to "no cache": this
    is a latency optimisation and must never be able to break a run."""

    def __init__(self, path=None):
        self.path = path or os.environ.get("TOOLCHAIN_TAGS_CACHE") or self._default()
        self.data = {}
        self.dirty = False
        try:
            with open(self.path) as handle:
                loaded = json.load(handle)
            if isinstance(loaded, dict):
                self.data = loaded
        except Exception:
            pass

    @staticmethod
    def _default():
        try:
            gitdir = git("rev-parse", "--absolute-git-dir")
        except Exception:
            return os.devnull
        return os.path.join(gitdir, "tauceti", "toolchain-tags-cache.json")

    @staticmethod
    def _key(key):
        return "\t".join(str(part) for part in key)

    def get(self, key):
        return self.data.get(self._key(key))

    def put(self, key, value):
        self.data[self._key(key)] = value
        self.dirty = True

    def flush(self):
        if not self.dirty or self.path == os.devnull:
            return
        try:
            os.makedirs(os.path.dirname(self.path), exist_ok=True)
            with open(self.path, "w") as handle:
                json.dump(self.data, handle)
        except Exception:
            pass


class Upstream:
    """Every read of mathlib, and the few reads of this repository's refs.

    Exactly seven request shapes, so the offline fake in the tests has a small
    surface and can reject anything it does not recognise."""

    def __init__(self, repo=MATHLIB, cache=None):
        self.repo = repo
        self.cache = cache if cache is not None else Cache()
        self.calls = 0
        self._repo_tags = None
        self._release_branches = None

    # ----- mathlib

    def release_tags(self):
        """{release name: tag object sha} for every mathlib tag that names a Lean
        release. Mutable (new releases appear), so never cached."""
        self.calls += 1
        raw = _gh(f"repos/{self.repo}/git/matching-refs/tags/v",
                  jq='.[] | [.ref, .object.sha, .object.type] | @tsv')
        out = {}
        for line in raw.splitlines():
            ref, sha, kind = line.split("\t")
            name = ref.rsplit("/", 1)[-1]
            if not is_release(name):
                continue
            out[name] = self.peel(sha, kind)
        return out

    def peel(self, sha, kind):
        """A tag ref can point at a tag object rather than a commit. mathlib's are
        lightweight today, so this is defensive, but a heavyweight tag would
        otherwise make every later lookup use the wrong sha."""
        if kind != "tag":
            return sha
        cached = self.cache.get(("peel", sha))
        if cached:
            return cached
        self.calls += 1
        target = _gh(f"repos/{self.repo}/git/tags/{sha}", jq=".object.sha").strip()
        self.cache.put(("peel", sha), target)
        return target

    def toolchain_at(self, sha):
        cached = self.cache.get(("toolchain", sha))
        if cached:
            return cached
        self.calls += 1
        value = _gh(f"repos/{self.repo}/contents/lean-toolchain?ref={sha}",
                    jq=".content").strip()
        value = _b64(value).strip()
        self.cache.put(("toolchain", sha), value)
        return value

    def manifest_at(self, sha):
        cached = self.cache.get(("manifest", sha))
        if cached:
            return cached
        self.calls += 1
        value = _b64(_gh(f"repos/{self.repo}/contents/lake-manifest.json?ref={sha}",
                         jq=".content").strip())
        self.cache.put(("manifest", sha), value)
        return value

    def parents(self, sha):
        cached = self.cache.get(("parents", sha))
        if cached is not None:
            return cached
        self.calls += 1
        raw = _gh(f"repos/{self.repo}/git/commits/{sha}", jq="[.parents[].sha] | @tsv")
        value = raw.split()
        self.cache.put(("parents", sha), value)
        return value

    def committed_at(self, sha):
        cached = self.cache.get(("date", sha))
        if cached:
            return cached
        self.calls += 1
        value = _gh(f"repos/{self.repo}/git/commits/{sha}", jq=".committer.date").strip()
        self.cache.put(("date", sha), value)
        return value

    def compare(self, base, head):
        """`.status` of base...head: ahead, behind, identical or diverged. Between two
        immutable SHAs the answer is immutable too, so it is cached; a symbolic head
        such as `master` is not."""
        immutable = _is_sha(base) and _is_sha(head)
        if immutable:
            cached = self.cache.get(("compare", base, head))
            if cached:
                return cached
        self.calls += 1
        value = _gh(f"repos/{self.repo}/compare/{base}...{head}", jq=".status").strip()
        if immutable:
            self.cache.put(("compare", base, head), value)
        return value

    def ahead_by(self, base, head):
        """How many commits `head` is ahead of `base`. Immutable between two shas."""
        cached = self.cache.get(("aheadby", base, head))
        if cached is not None:
            return cached
        self.calls += 1
        value = int(_gh(f"repos/{self.repo}/compare/{base}...{head}", jq=".ahead_by").strip())
        self.cache.put(("aheadby", base, head), value)
        return value

    def is_ancestor(self, ancestor, descendant):
        """Whether `ancestor` is an ancestor of, or equal to, `descendant`.

        The same primitive, and the same reading of `.status`, that
        `scripts/check-bump.sh` step 2 uses to decide a bump moved forward."""
        if ancestor == descendant:
            return True
        return self.compare(ancestor, descendant) in ("ahead", "identical")

    def on_master(self, sha):
        return self.compare(sha, "master") in ("ahead", "identical")

    def is_toolchain_bump_commit(self, sha):
        """Whether `sha` is the first commit carrying its own toolchain, i.e. its
        parent's toolchain differs.

        Mathlib has tagged releases this way since v4.28.0, and that habit is what
        lets ancestry be decided by comparing toolchains. It is a habit, not a
        contract: `v4.24.0`, `v4.25.0` and `v4.27.0` sit on commits whose parent
        already carried the same toolchain. So this is asserted per release, and the
        caller falls back to real ancestry queries when it does not hold."""
        parents = self.parents(sha)
        if len(parents) != 1:
            return False
        return self.toolchain_at(sha) != self.toolchain_at(parents[0])

    # ----- this repository

    def _matching_refs(self, prefix):
        """{short name: (sha, object type)} for one `git/matching-refs` query.

        One call for a whole namespace rather than one per release. Asking for eleven
        tags individually is eleven round trips, and in a repository that has no tags
        yet every one of them is a 404."""
        self.calls += 1
        raw = _gh_optional(f"repos/{REPO}/git/matching-refs/{prefix}",
                           jq='.[] | [.ref, .object.sha, .object.type] | @tsv') or ""
        full = f"refs/{prefix}"
        out = {}
        for line in raw.splitlines():
            ref, sha, kind = line.split("\t")
            out[ref[len(full):] if ref.startswith(full) else ref] = (sha, kind)
        return out

    def repo_tags(self):
        if self._repo_tags is None:
            self._repo_tags = self._matching_refs("tags/v")
        return self._repo_tags

    def release_branches(self):
        if self._release_branches is None:
            self._release_branches = self._matching_refs("heads/releases/")
        return self._release_branches

    def tag_target(self, release):
        """The commit a tag points at, peeled, or None when there is no such tag."""
        entry = self.repo_tags().get(release)
        if not entry:
            return None
        sha, kind = entry
        if kind != "tag":
            return sha
        self.calls += 1
        return _gh(f"repos/{REPO}/git/tags/{sha}", jq=".object.sha").strip()

    def repo_pin_at(self, sha):
        """(toolchain, mathlib rev) at a commit of THIS repository, read through the
        API rather than git: a tag's target may be a release-branch commit that a
        given checkout has never fetched. Immutable, so cached."""
        cached = self.cache.get(("repopin", sha))
        if cached:
            return tuple(cached)
        self.calls += 2
        toolchain = _b64(_gh(f"repos/{REPO}/contents/lean-toolchain?ref={sha}",
                             jq=".content").strip()).strip()
        manifest = _b64(_gh(f"repos/{REPO}/contents/lake-manifest.json?ref={sha}",
                            jq=".content").strip())
        rev = None
        for pkg in json.loads(manifest).get("packages", []):
            if pkg.get("name") == "mathlib":
                rev = pkg.get("rev")
        self.cache.put(("repopin", sha), [toolchain, rev])
        return toolchain, rev

    def branch_head(self, branch):
        short = branch[len("releases/"):] if branch.startswith("releases/") else branch
        entry = self.release_branches().get(short)
        return entry[0] if entry else None

    def verify_conclusion(self, sha):
        """The newest conclusion of the release workflow on this commit, or None when
        it has never run there. `None` means "not built yet", never "failed"."""
        self.calls += 1
        raw = _gh_optional(
            f"repos/{REPO}/actions/workflows/{VERIFY_WORKFLOW}/runs"
            f"?head_sha={sha}&per_page=20",
            jq='[.workflow_runs[] | select(.status == "completed") | .conclusion] | .[0] // ""')
        return (raw or "").strip() or None


def _b64(content):
    import base64
    return base64.b64decode(content).decode()


def _is_sha(value):
    return bool(re.fullmatch(r"[0-9a-f]{40}", value or ""))


# --- base derivation ---------------------------------------------------------

def find_exact_run(segments, toolchain, mathlib_rev):
    """The segment pinning exactly (toolchain, mathlib_rev), or None.

    At most one can exist: a segment is a maximal run of one state, and main's pin
    only ever moves forward, so a state never recurs."""
    for seg in segments:
        if seg["toolchain"] == toolchain and seg["mathlib_rev"] == mathlib_rev:
            return seg
    return None


def first_on_toolchain(segments, toolchain):
    for seg in segments:
        if seg["toolchain"] == toolchain:
            return seg
    return None


def _last_true(count, predicate):
    """Index of the last i < count with predicate(i), or -1.

    Binary search, valid because the predicate is monotone: main's pin advances, so
    once a pin has passed M every later pin has too."""
    low, high, found = 0, count - 1, -1
    while low <= high:
        mid = (low + high) // 2
        if predicate(mid):
            found = mid
            low = mid + 1
        else:
            high = mid - 1
    return found


def resolve_base(segments, release, mathlib_rev, up):
    """(segment, rule) for the last main segment whose pin is an ancestor-or-equal of
    the mathlib tag commit, or (None, rule) when the repository has no such commit.

    `rule` is `toolchain-fast-path` or `ancestry-search`, and says which decision
    procedure was used, so the audit can show its working."""
    usable = [seg for seg in segments if seg["mathlib_rev"]]
    if not usable:
        return None, "none"

    fast = False
    try:
        fast = up.on_master(mathlib_rev) and up.is_toolchain_bump_commit(mathlib_rev)
    except RuntimeError:
        fast = False

    if fast:
        # M is the first master commit carrying toolchain X, so for a pin p on master:
        # toolchain(p) < X means p precedes M, toolchain(p) > X means p follows it, and
        # toolchain(p) == X means p is M itself or a descendant. No API call per pin.
        target = release
        rule = "toolchain-fast-path"

        def holds(index):
            seg = usable[index]
            name = release_of_toolchain(seg["toolchain"])
            if name is None:
                return False
            if release_lt(name, target):
                return True
            return seg["mathlib_rev"] == mathlib_rev
    else:
        rule = "ancestry-search"

        def holds(index):
            return up.is_ancestor(usable[index]["mathlib_rev"], mathlib_rev)

    found = _last_true(len(usable), holds)
    if found < 0:
        return None, rule
    base = usable[found]
    # Verify the fast path's answer with one real ancestry query. The premise it rests
    # on is an upstream habit rather than a contract, so the saving is worth one call
    # but not the risk of trusting it unchecked.
    if rule == "toolchain-fast-path" and not up.is_ancestor(base["mathlib_rev"], mathlib_rev):
        rule = "ancestry-search"
        found = _last_true(len(usable), lambda i: up.is_ancestor(usable[i]["mathlib_rev"],
                                                                 mathlib_rev))
        if found < 0:
            return None, rule
        base = usable[found]
    return base, rule


# --- the release commit's two files ------------------------------------------

def parse_manifest(text):
    return json.loads(text)


def render_manifest(obj):
    """Lake's exact `lake-manifest.json` layout, so a derived manifest is a minimal
    diff against the one Lake last wrote.

    Reproduced from the bytes rather than guessed: root entries are separated by
    `,\\n ` (one space), the packages array sits on its own line with the same one
    space, package objects are separated by `,\\n  ` (two), and keys within a package
    by `,\\n   ` (three, which aligns them under both `[{` and ` {`). A round-trip
    test against the repository's own manifest is what keeps this honest."""
    def scalar(value):
        return json.dumps(value)

    def package(pkg):
        body = ",\n   ".join(f"{scalar(k)}: {scalar(v)}" for k, v in pkg.items())
        return "{" + body + "}"

    parts = []
    for key, value in obj.items():
        if key == "packages":
            packages = ",\n  ".join(package(p) for p in value)
            parts.append(f'{scalar(key)}:\n [{packages}]')
        else:
            parts.append(f"{scalar(key)}: {scalar(value)}")
    return "{" + ",\n ".join(parts) + "}\n"


def derive_manifest(base_manifest, mathlib_manifest, mathlib_rev):
    """The manifest a release commit carries: this repository's own root fields, its
    own mathlib entry repointed at `mathlib_rev`, and mathlib's entire dependency set
    at that revision.

    Every rule here mirrors a step of `scripts/check-bump.sh`, so the result passes
    bump-guard by construction. Note that bump-guard compares the tuple
    `(type, normalised url, rev, inputRev)` and not literally every field, which is
    why `inherited` may be normalised below without contradicting it."""
    base = parse_manifest(base_manifest)
    upstream = parse_manifest(mathlib_manifest)

    ours = [p for p in base.get("packages", []) if p.get("name") == "mathlib"]
    if len(ours) != 1:
        raise ValueError(f"expected exactly one mathlib package in the base, found {len(ours)}")
    mathlib_pkg = dict(ours[0])
    if mathlib_pkg.get("inputRev") != "master":
        raise ValueError(
            f"base pins mathlib at inputRev {mathlib_pkg.get('inputRev')!r}, not 'master'; "
            "the nominated branch is human-owned and a release commit never changes it")
    if not _is_sha(mathlib_rev):
        raise ValueError(f"mathlib rev {mathlib_rev!r} is not a 40-hex commit sha")
    mathlib_pkg["rev"] = mathlib_rev

    deps = []
    for pkg in upstream.get("packages", []):
        if pkg.get("name") == "mathlib":
            raise ValueError("mathlib's own manifest lists a package named mathlib")
        if pkg.get("type") != "git":
            raise ValueError(f"upstream package {pkg.get('name')!r} is not a git package")
        if not _is_sha(pkg.get("rev")):
            raise ValueError(f"upstream package {pkg.get('name')!r} has a non-sha rev")
        # Every mathlib dependency is transitive from here, whatever mathlib itself
        # recorded: mathlib marks its own direct deps `false`, and Lake writes `true`
        # for all of ours. Assigning through dict() keeps the key in its original place.
        deps.append(dict(pkg, inherited=True))

    names = [p.get("name") for p in deps] + ["mathlib"]
    duplicates = sorted({n for n in names if names.count(n) > 1})
    if duplicates:
        raise ValueError(f"duplicate package names in the derived manifest: {duplicates}")

    out = {}
    for key, value in base.items():
        if key == "packages":
            out["packages"] = [mathlib_pkg] + deps
        elif key == "version":
            # Lake's manifest-format version, written by the Lake that ships with the
            # target toolchain, so mathlib's copy at M is the right one and the base's
            # may be stale. Every other root field (name, lakeDir, packagesDir,
            # fixedToolchain, and anything Lake adds later) is ours and is preserved.
            out["version"] = upstream.get("version", value)
        else:
            out[key] = value
    return render_manifest(out)


def derive_toolchain(base_toolchain, release):
    """`leanprover/lean4:vX`, keeping the base file's trailing-newline convention.
    mathlib's file ends with one and this repository's does not; matching mathlib
    byte for byte would add a gratuitous whitespace diff, and bump-guard strips
    whitespace when it compares."""
    text = toolchain_for(release)
    return text + "\n" if (base_toolchain or "").endswith("\n") else text


# --- classification ----------------------------------------------------------

STATUSES = ("tagged", "verified", "ready", "branch-ready", "needs-branch", "blocked",
            "out-of-scope")


def _target_of(segments, release, mathlib_rev, up):
    """(target_sha, kind, exact, base_segment, base_rule) for the commit that should
    carry this release's tag, with target_sha None when none can be named yet.

    `kind` is `main-commit` or `release-branch`. RUN_TAG_POLICY decides which commit
    of an exact-pin run is chosen; see its comment for why it is not a free choice."""
    toolchain = toolchain_for(release)
    run = find_exact_run(segments, toolchain, mathlib_rev)
    if run is not None:
        return run[f"{RUN_TAG_POLICY}_sha"], "main-commit", True, None, "exact-on-main"

    branch = RELEASE_BRANCH_FMT.format(release=release)
    head = up.branch_head(branch)
    if head:
        return head, "release-branch", True, None, "release-branch"

    base, rule = resolve_base(segments, release, mathlib_rev, up)
    if base is not None:
        return None, "release-branch", True, base, rule

    # No forward base exists, so the exact pin is unreachable. Fall back to the
    # inexact rung when main did traverse this toolchain; when it did not, nothing
    # can be tagged, because mathlib's own oleans exist only for mathlib's commits
    # at that toolchain and a pin elsewhere would not build.
    era = first_on_toolchain(segments, toolchain)
    if era is not None:
        return (era[f"{RUN_TAG_POLICY}_sha"], "main-commit", False, None,
                "inexact-first-on-toolchain")
    return None, None, True, None, rule


def _tag_is_valid(tag_sha, release, mathlib_rev, up):
    """(ok, why-not, exact) for a tag that already exists.

    Rung-aware: an exact tag pins the mathlib tag commit itself, an inexact one pins a
    master descendant of it. Both must carry the release's own toolchain."""
    toolchain, pin = up.repo_pin_at(tag_sha)
    want = toolchain_for(release)
    if toolchain != want:
        return False, f"is on {toolchain or 'no toolchain'}, not {want}", True
    if pin == mathlib_rev:
        return True, None, True
    if pin and up.is_ancestor(mathlib_rev, pin):
        return True, None, False
    return False, (f"pins mathlib {(pin or 'nothing')[:8]}, which is not the {release} tag "
                   "commit nor a descendant of it"), False


def classify(release, mathlib_rev, segments, up):
    """One row of the audit. Exactly one terminal status per release."""
    toolchain = toolchain_for(release)
    row = {
        "release": release, "toolchain": toolchain, "mathlib_rev": mathlib_rev,
        "status": None, "reason": None, "target_sha": None, "target_kind": None,
        "exact": True, "distance": None, "base_sha": None, "base_index": None,
        "base_rule": None, "branch": RELEASE_BRANCH_FMT.format(release=release),
        "verify": None, "tag_sha": None,
    }

    oldest = release_of_toolchain(segments[0]["toolchain"])
    if oldest is not None and release_lt(release, oldest):
        row["status"] = "out-of-scope"
        row["reason"] = f"predates this repository, whose history starts on {oldest}"
        return row

    target, kind, exact, base, rule = _target_of(segments, release, mathlib_rev, up)
    row.update(target_sha=target, target_kind=kind, exact=exact, base_rule=rule)
    if base is not None:
        row.update(base_sha=base["last_sha"], base_index=base["last_index"])

    if not exact and target:
        row["distance"] = _distance(segments, target, mathlib_rev, up)

    tag_sha = up.tag_target(release)
    row["tag_sha"] = tag_sha
    if tag_sha:
        # Judge an existing tag by the pins it actually carries, not by re-deriving
        # what policy would name today. Otherwise deleting a `releases/vX` branch
        # after tagging, which is harmless, would read as a tag mismatch.
        ok, why, exact = _tag_is_valid(tag_sha, release, mathlib_rev, up)
        row["exact"] = exact
        if ok:
            row["status"] = "tagged"
            row["target_sha"], row["target_kind"] = tag_sha, row["target_kind"]
        else:
            row["status"] = "blocked"
            row["reason"] = (f"the tag at {tag_sha[:8]} {why}; a published tag is never "
                             "moved, so a human decides what to do")
        return row

    if target is None:
        if row["base_sha"]:
            # The base exists, so an exact release commit can be constructed; there is
            # simply no commit to name until someone does.
            row["status"] = "needs-branch"
            return row
        row["status"] = "blocked"
        row["reason"] = (
            "no main commit pins an ancestor of the mathlib tag, and main never ran on "
            f"{toolchain}, so neither an exact nor an inexact commit exists")
        return row

    row["verify"] = up.verify_conclusion(target)
    if row["verify"] == "success":
        row["status"] = "verified"
    elif row["verify"] in ("failure", "timed_out", "startup_failure"):
        row["status"] = "blocked"
        row["reason"] = (f"the release build on {target[:8]} concluded {row['verify']}; "
                         "it needs a release build that passes, which is not the same as "
                         "saying this release cannot be built")
    elif row["target_kind"] == "release-branch" and row["target_sha"]:
        row["status"] = "branch-ready"
    elif row["target_kind"] == "release-branch":
        row["status"] = "needs-branch"
    else:
        row["status"] = "ready"
    return row


def _distance(segments, target_sha, mathlib_rev, up):
    """How many mathlib commits the target's pin sits past the release tag. Recorded
    in an inexact tag's message, and checked against the graph rather than trusted."""
    for seg in segments:
        if seg["first_sha"] != target_sha:
            continue
        pin = seg["mathlib_rev"]
        if not pin or pin == mathlib_rev:
            return 0
        try:
            return up.ahead_by(mathlib_rev, pin)
        except (RuntimeError, ValueError):
            return None
    return None


def audit(segments, up, only=None):
    """One row per mathlib release tag, newest last."""
    assert_monotone(segments)
    tags = up.release_tags()
    rows = []
    for release in sorted(tags, key=release_key):
        if only and release != only:
            continue
        rows.append(classify(release, tags[release], segments, up))
    return rows


def actionable(rows):
    return [r for r in rows if r["status"] in ("verified", "ready", "branch-ready",
                                               "needs-branch", "blocked")]


# --- rendering ---------------------------------------------------------------

POLICY_TEXT = """\
Tau Ceti toolchain tags
=======================

For every Lean release X that this repository's history can reach, the tag `vX`
points at the FIRST main-reachable commit whose lean-toolchain is exactly
`leanprover/lean4:X` and whose mathlib pin is at or after mathlib's own `vX` tag
commit M. The pin is, in order of preference:

  1. exact   -- M itself. The commit is either already on main, or is a single
                commit on a `releases/vX` branch whose parent is a main commit and
                which changes ONLY lake-manifest.json and lean-toolchain.
  2. inexact -- when no exact commit exists or the exact one will not compile, the
                first main commit on toolchain X. The tag message records how many
                mathlib commits past M the pin is.

A tag is created only after a from-source build of that commit passes the audits and
lints main runs, and its oleans have been published to the Lake cache and read back.
That build, publish and tag is `.github/workflows/release-tag.yml`; this tool never
builds, pushes or tags anything itself.

Tags are NEVER moved. If a tag exists but disagrees with the policy, that is a
question for a human, and no instruction below will ever delete or force a tag.

What the cache promise covers: this repository publishes its OWN oleans, and
mathlib's come from mathlib's cache. Where mathlib published no cache for a release,
which is the case for tags it cut on its `stable` branch, a consumer must compile
mathlib whatever we do.
"""

_STATUS_BLURB = {
    "tagged": "done",
    "verified": "built and published; the tag is all that is missing",
    "ready": "an exact commit exists on main and needs a release build",
    "branch-ready": "the release branch exists and needs a release build",
    "needs-branch": "the release commit has to be constructed first",
    "blocked": "needs a human",
    "out-of-scope": "predates this repository",
}


def render_table(rows, show_all=False):
    head = f"{'release':14s} {'status':13s} {'pin':8s} {'target':9s} {'note'}"
    lines = [head, "-" * max(len(head), 76)]
    skipped = [r for r in rows if r["status"] == "out-of-scope"]
    if skipped and not show_all:
        span = (skipped[0]["release"] if len(skipped) == 1
                else f"{skipped[0]['release']} to {skipped[-1]['release']}")
        lines.append(f"({len(skipped)} release{'' if len(skipped) == 1 else 's'} "
                     f"({span}) predate this repository; --all to list them)")
        rows = [r for r in rows if r["status"] != "out-of-scope"]
    for row in rows:
        target = (row["target_sha"] or "")[:8] or "-"
        pin = "exact" if row["exact"] else "inexact"
        note = row["reason"] or _STATUS_BLURB.get(row["status"], "")
        if row["status"] == "ready" and not row["exact"]:
            note = "no exact commit is reachable; needs a release build on the inexact rung"
        if row["status"] == "needs-branch" and row["base_sha"]:
            note = f"base {row['base_sha'][:8]} (main #{row['base_index']})"
        if not row["exact"] and row["distance"] is not None:
            note = f"{note}; pin is {row['distance']} mathlib commits past the tag"
        lines.append(f"{row['release']:14s} {row['status']:13s} {pin:8s} {target:9s} {note}")
    return "\n".join(lines)


def recipe_for(row):
    """Literal, copy-pasteable repair instructions for one release. These are what an
    agent acts on, so they name every sha in full and never abbreviate a command."""
    release, status = row["release"], row["status"]
    dispatch = (f"    gh workflow run release-tag.yml -f release={release} "
                f"-f sha={row['target_sha']} -f exact={'true' if row['exact'] else 'false'}")
    if status == "out-of-scope":
        return None
    if status == "tagged":
        return None
    if status == "verified":
        return (f"{release} -- verified\n"
                f"  {row['target_sha']} was built from source and published, but carries no\n"
                f"  tag. Re-dispatch the release workflow; its tag job is idempotent and will\n"
                f"  create the tag without rebuilding anything that already succeeded:\n"
                f"{dispatch}\n")
    if status in ("ready", "branch-ready"):
        if row["target_kind"] != "main-commit":
            where = f"the head of {row['branch']}, pinning mathlib's {release} tag"
        elif row["exact"]:
            where = "a commit on main pinning mathlib's tag exactly"
        else:
            where = "the first main commit on the release's toolchain"
        extra = ""
        if not row["exact"]:
            extra = ("  No exact pin is reachable for this release, so this is the inexact\n"
                     f"  rung, and the pin sits {row['distance']} mathlib commits past the tag.\n")
        return (f"{release} -- {status}\n"
                f"  {row['target_sha']} is {where}. It needs a from-source build, a cache\n"
                f"  publish and a tag:\n{extra}{dispatch}\n")
    if status == "needs-branch":
        base = row["base_sha"]
        return (f"{release} -- needs-branch\n"
                f"  main never pinned mathlib's {release} tag ({row['mathlib_rev']}), so the\n"
                f"  release commit has to be constructed. Its base is {base}\n"
                f"  (main #{row['base_index']}), the last main commit whose pin is an ancestor\n"
                f"  of the tag, so the pin only moves forward:\n\n"
                f"    git fetch origin main\n"
                f"    git checkout -b {row['branch']} {base}\n"
                f"    python3 scripts/toolchain_tags.py --write {release} --dir .\n"
                f"    git commit -am 'chore: release commit for Lean {release}'\n"
                f"    git push origin {row['branch']}\n"
                f"    python3 scripts/toolchain_tags.py --audit --release {release}"
                f"   # expect: branch-ready\n\n"
                f"  Then dispatch the release workflow on the branch head. The branch must\n"
                f"  differ from its base in the two pin files and nothing else; a compile fix\n"
                f"  belongs on main, after which re-cut the branch.\n")
    if status == "blocked":
        return (f"{release} -- blocked\n  {row['reason']}\n")
    return None


def render_audit(rows, show_all=False):
    parts = [POLICY_TEXT, "", render_table(rows, show_all), ""]
    recipes = [r for r in (recipe_for(row) for row in actionable(rows)) if r]
    if recipes:
        parts += ["Repairs", "-------", ""] + recipes
    else:
        parts += ["Every reachable release is tagged.", ""]
    return "\n".join(parts)


def rows_to_json(rows):
    return json.dumps(rows, indent=2, sort_keys=True)


def tag_message(row):
    """The annotated tag body. The trailing marker carries the same facts in machine
    form so a later audit can read back what was claimed at tagging time."""
    exact = "yes" if row["exact"] else f"no, {row['distance']} mathlib commits past the tag"
    meta = {
        "schema": 1, "release": row["release"], "toolchain": row["toolchain"],
        "mathlib_rev": row["mathlib_rev"], "mathlib_tag": row["release"],
        "exact": bool(row["exact"]), "distance": row["distance"],
        "kind": row["target_kind"], "commit": row["target_sha"],
    }
    return (
        f"TauCeti {row['release']}\n\n"
        f"Lean toolchain: {row['toolchain']}\n"
        f"Mathlib:        {row['mathlib_rev']} ({MATHLIB} {row['release']})\n"
        f"Commit:         {row['target_sha']} ({row['target_kind']})\n"
        f"Exact pin:      {exact}\n\n"
        f"Built from source with the Lake artifact cache disabled, audited and linted\n"
        f"exactly as main is, and published to the Lake cache.\n\n"
        f"<!--tauceti-toolchain-tag:v1 {json.dumps(meta, sort_keys=True)}-->\n")


def parse_tag_message(message):
    """The marker's payload, or None. Anchored to the end and strictly shaped, so
    text quoting a marker earlier in the body cannot be read as the real one."""
    match = _TAG_MARKER_RE.search(message or "")
    if not match:
        return None
    try:
        return json.loads(match.group(1))
    except ValueError:
        return None


# --- Zulip ------------------------------------------------------------------
#
# The marker-and-reconcile idiom below is copied from scripts/pr_status/stuck_alerts.py
# (`parse_marker` through `reconcile`), which is the source of truth for it. It is
# copied rather than shared: that module is the emergency watchdog, and refactoring a
# live detector to take a marker parameter for a new feature's convenience is the
# wrong trade. Keep the two in step by hand if the idiom changes.

KEY_RE = re.compile(r"[a-z0-9][a-z0-9._/-]*")
MARKER_RE = re.compile(r"<!--toolchain-tag:v1 (" + KEY_RE.pattern + r")-->\s*\Z")
RED = "\U0001f534"
GREEN = "✅"


def key_prefix(key):
    return key.split("/", 1)[0]


def parse_marker(content):
    match = MARKER_RE.search(content or "")
    return match.group(1) if match else None


def alert_content(alert):
    return (f"{RED} **{alert['title']}**\n\n{alert['body']}\n\n"
            f"<!--toolchain-tag:v1 {alert['key']}-->")


def resolved_content(key, title):
    return (f"{GREEN} **{title}** — cleared\n\n_No longer outstanding as of the latest "
            f"check._\n\n<!--toolchain-tag:v1 {key}-->")


def newest_by_key(msgs, bot_id):
    out = {}
    for msg in msgs:
        if msg["sender_id"] != bot_id:
            continue
        key = parse_marker(msg["content"])
        if key is None:
            continue
        if key not in out or msg["id"] > out[key]["id"]:
            out[key] = msg
    return out


def is_resolved(msg):
    return msg["content"].lstrip().startswith(GREEN)


def alerts_from(rows, up, now=None):
    """One alert per release that needs attention.

    Blocked releases alert immediately. The merely actionable ones wait out a grace
    period measured from mathlib's own tag date, so the automation gets first crack at
    a release before anyone is woken about it."""
    import datetime
    now = now or datetime.datetime.now(datetime.timezone.utc)
    out = []
    for row in rows:
        if row["status"] in ("tagged", "out-of-scope", "verified"):
            continue
        if row["status"] != "blocked":
            try:
                cut = datetime.datetime.fromisoformat(
                    up.committed_at(row["mathlib_rev"]).replace("Z", "+00:00"))
            except Exception:
                cut = None
            if cut and (now - cut).total_seconds() < GRACE_HOURS * 3600:
                continue
        title = f"{row['release']} has no toolchain tag ({row['status']})"
        body = zp.zulip_sanitize(recipe_for(row) or row["reason"] or "")
        out.append({"key": f"{row['status']}/{row['release']}".lower(),
                    "title": zp.zulip_sanitize(title), "body": body})
    return out


def reconcile(z, alerts, failed, dry_run):
    bot_id = z.my_user_id()
    msgs = z.get_messages([
        {"operator": "channel", "operand": zp.CHANNEL},
        {"operator": "topic", "operand": zp.TOPIC},
    ])
    existing = newest_by_key(msgs, bot_id)
    active = {a["key"]: a for a in alerts}

    for key, alert in active.items():
        content = alert_content(alert)
        msg = existing.get(key)
        if msg is None or is_resolved(msg):
            zp.log(f"POST alert {key}")
            if not dry_run:
                z.send_message(content)
        elif msg["content"] != content:
            zp.log(f"refresh alert {key}")
            if not dry_run:
                z.update_message(msg["id"], content)
        else:
            zp.log(f"ongoing alert {key} (unchanged)")

    for key, msg in existing.items():
        if key in active or is_resolved(msg):
            continue
        if key_prefix(key) in failed:
            zp.log(f"classification for {key} failed this run; NOT resolving (fail closed)")
            continue
        zp.log(f"RESOLVED alert {key}")
        if not dry_run:
            z.update_message(msg["id"], resolved_content(key, key))


# --- the other modes ---------------------------------------------------------

def next_stepping_stone(segments, up, target=None):
    """The mathlib rev the daily bump should pin instead of its last-known-good
    commit, or None.

    A release qualifies when main's pin has not reached its tag but the bump's target
    has passed it, the tag is on master (a `stable`-branch patch release could never
    satisfy bump-guard, so it is backfill-only by construction), and the move is
    forward from main's current pin."""
    current = segments[-1]
    head = target or "master"
    reached = release_of_toolchain(up.toolchain_at(head))
    here = release_of_toolchain(current["toolchain"])
    if reached is None or here is None:
        return None
    tags = up.release_tags()
    for release in sorted(tags, key=release_key):
        if not release_lt(here, release) or release_lt(reached, release):
            continue
        rev = tags[release]
        if rev == current["mathlib_rev"]:
            continue
        if not up.on_master(rev):
            continue
        if not up.is_ancestor(current["mathlib_rev"], rev):
            continue
        return rev
    return None


def write_release_files(directory, release, mathlib_rev, base_sha, up):
    """Materialise the two pin files of a release commit. Returns the paths written."""
    base_manifest = blob_at(base_sha, "lake-manifest.json")
    base_toolchain = blob_at(base_sha, "lean-toolchain")
    if not base_manifest or not base_toolchain:
        raise RuntimeError(f"{base_sha} is missing a pin file; is it fetched?")
    manifest = derive_manifest(base_manifest, up.manifest_at(mathlib_rev), mathlib_rev)
    toolchain = derive_toolchain(base_toolchain, release)
    upstream_toolchain = up.toolchain_at(mathlib_rev).strip()
    if upstream_toolchain != toolchain_for(release):
        raise RuntimeError(
            f"mathlib at {mathlib_rev[:8]} is on {upstream_toolchain}, not "
            f"{toolchain_for(release)}; that tag does not name the release it claims to")
    written = []
    for name, text in (("lake-manifest.json", manifest), ("lean-toolchain", toolchain)):
        path = os.path.join(directory, name)
        with open(path, "w") as handle:
            handle.write(text)
        written.append(path)
    return written


# --- CLI ---------------------------------------------------------------------

def _row_for(release, segments, up):
    tags = up.release_tags()
    if release not in tags:
        raise RuntimeError(f"{MATHLIB} has no release tag named {release}")
    return classify(release, tags[release], segments, up)


def _run_audit(args, segments, up):
    rows = audit(segments, up, only=args.audit_release)
    if args.json:
        print(rows_to_json(rows))
    else:
        print(render_audit(rows, args.all))
    if args.strict and any(r["status"] == "blocked" for r in rows):
        return 1
    return 0


def _run_write(args, segments, up):
    row = _row_for(args.write, segments, up)
    base = args.base or row["base_sha"]
    if not base:
        print(f"no base commit for {args.write}: {row['reason'] or row['status']}",
              file=sys.stderr)
        return 1
    if args.dry_run:
        manifest = derive_manifest(blob_at(base, "lake-manifest.json"),
                                   up.manifest_at(row["mathlib_rev"]), row["mathlib_rev"])
        print(derive_toolchain(blob_at(base, "lean-toolchain"), args.write))
        print(manifest, end="")
        return 0
    for path in write_release_files(args.dir, args.write, row["mathlib_rev"], base, up):
        print(f"wrote {path}")
    return 0


def _run_alert(args, segments, up):
    rows, failed = [], set()
    try:
        rows = audit(segments, up)
    except Exception as exc:  # fail closed: resolve nothing when the audit itself broke
        zp.log(f"audit failed (non-fatal): {exc}")
        failed = set(STATUSES)
    alerts = alerts_from(rows, up) if rows else []
    zp.log(f"{len(alerts)} outstanding release(s): {sorted(a['key'] for a in alerts)}")

    if args.dry_run:  # never touches Zulip, with or without credentials
        for alert in alerts:
            print("\n" + alert_content(alert))
        return 0

    email = (os.environ.get("ZULIP_EMAIL") or "").strip()
    api_key = (os.environ.get("ZULIP_API_KEY") or "").strip()
    site = (os.environ.get("ZULIP_SITE") or "https://leanprover.zulipchat.com").strip()
    if not (email and api_key):
        return zp.fail_config("ZULIP_EMAIL / ZULIP_API_KEY not set (no bot configured)")
    z = zp.Zulip(email, api_key, site)
    try:
        zp.check(z)
        reconcile(z, alerts, failed, args.dry_run)
    except zp.ConfigError as exc:
        return zp.fail_config(str(exc))
    except Exception as exc:  # a transient Zulip hiccup is cosmetic and self-heals
        zp.log(f"reconcile failed (non-fatal): {exc}")
    return 0


def build_parser():
    ap = argparse.ArgumentParser(
        description="Audit and materialise Tau Ceti's Lean toolchain tags.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=POLICY_TEXT)
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--audit", action="store_true",
                      help="report every release and how to repair the gaps (default)")
    mode.add_argument("--next-stepping-stone", action="store_true",
                      help="print the mathlib rev the daily bump should pin first")
    mode.add_argument("--write", metavar="vX",
                      help="materialise a release commit's two pin files")
    mode.add_argument("--tag-message", metavar="vX",
                      help="print the annotated tag body for a release")
    mode.add_argument("--alert", action="store_true",
                      help="reconcile the outstanding releases against Zulip")
    ap.add_argument("--release", dest="audit_release", metavar="vX",
                    help="with --audit, report only this release")
    ap.add_argument("--json", action="store_true", help="with --audit, the machine worklist")
    ap.add_argument("--all", action="store_true",
                    help="with --audit, list the releases that predate this repository too")
    ap.add_argument("--strict", action="store_true",
                    help="with --audit, exit 1 when any release is blocked")
    ap.add_argument("--target", help="with --next-stepping-stone, the bump's target rev")
    ap.add_argument("--dir", default=".", help="with --write, where to put the files")
    ap.add_argument("--base", help="with --write, override the derived base commit")
    ap.add_argument("--dry-run", action="store_true", help="print, do not write or post")
    return ap


def main(argv=None):
    args = build_parser().parse_args(argv)
    up = Upstream()
    try:
        segments = compute_segments()
        if args.next_stepping_stone:
            rev = next_stepping_stone(segments, up, args.target)
            if rev:
                print(rev)
            return 0
        if args.write:
            return _run_write(args, segments, up)
        if args.tag_message:
            print(tag_message(_row_for(args.tag_message, segments, up)), end="")
            return 0
        if args.alert:
            return _run_alert(args, segments, up)
        return _run_audit(args, segments, up)
    except RuntimeError as exc:
        print(f"toolchain_tags: {exc}", file=sys.stderr)
        return 2
    finally:
        up.cache.flush()


if __name__ == "__main__":
    sys.exit(main())
