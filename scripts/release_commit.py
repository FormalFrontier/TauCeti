#!/usr/bin/env python3
"""Decide whether a commit is a valid Tau Ceti release commit for a Lean release.

This is the file-comparison half of `scripts/check-release-commit.sh`, which is the
trust anchor that lets `.github/workflows/release-tag.yml` build a target commit
unsandboxed and publish its oleans. The shell driver does the GitHub orchestration
(which commit, which parent, which refs); everything here is pure text and JSON, so
it can be unit-tested without a network.

## What "valid" means

A release commit for release X carries exactly two facts:

  * `lean-toolchain` is `leanprover/lean4:X`, and equals mathlib's own `lean-toolchain`
    at mathlib's `X` tag commit M;
  * `lake-manifest.json` pins mathlib at M, keeps the url and the nominated branch the
    base recorded, and its remaining packages are exactly mathlib's own dependencies
    at M.

Those are checked as PROPERTIES, in the same terms `scripts/check-bump.sh` step 3 uses:
the tuple `(type, normalised url, rev, inputRev)` per package. Deliberately not by
re-deriving the file and diffing: `scripts/toolchain_tags.py` is what constructs a
release commit, and a verifier that shared its code, or reproduced its exact byte
output, would let a bug in the constructor certify itself. Fields the guard does not
constrain, `inherited` among them, are not compared, because whether Lake wrote `true`
or `false` there is not a fact about which mathlib is pinned.

## Usage

    release_commit.py check --release v4.33.0 --rev <mathlib sha> \\
        --pr-manifest pr/lake-manifest.json --pr-toolchain pr/lean-toolchain \\
        --base-manifest base/lake-manifest.json \\
        --mathlib-manifest mathlib.json --mathlib-toolchain mathlib-toolchain

Prints one line per problem and exits 1 when there is any; exits 0 and prints nothing
when the commit is a valid release commit. Only python3's standard library.
"""

from __future__ import annotations

import argparse
import json
import re
import sys

SHA_RE = re.compile(r"\A[0-9a-f]{40}\Z")
RELEASE_RE = re.compile(r"\Av\d+\.\d+\.\d+(?:-rc\d+)?\Z")
TOOLCHAIN_PREFIX = "leanprover/lean4:"

# Root fields that describe THIS package rather than its dependencies, and so must
# survive a release commit unchanged. `version` is excluded on purpose: it is Lake's
# manifest-format version, written by whichever Lake produced the file, and the release
# commit's Lake is the target toolchain's rather than the base's.
OWN_ROOT_FIELDS = ("name", "packagesDir", "lakeDir", "fixedToolchain")


def normalise_url(url):
    url = (url or "").rstrip("/")
    return url[:-4] if url.endswith(".git") else url


def identity(pkg):
    """The tuple `check-bump.sh` step 3 compares. Nothing outside it is a claim about
    which revision of a dependency is pinned."""
    return (pkg.get("type"), normalise_url(pkg.get("url")), pkg.get("rev"),
            pkg.get("inputRev"))


def packages_by_name(manifest, problems, label):
    out = {}
    for pkg in manifest.get("packages", []):
        name = pkg.get("name")
        if name in out:
            problems.append(f"{label} lists package {name!r} more than once")
        out[name] = pkg
    return out


def check_manifest(pr_text, base_text, mathlib_text, mathlib_rev):
    """Problems with a release commit's manifest, empty when there are none."""
    problems = []
    try:
        pr = json.loads(pr_text)
        base = json.loads(base_text)
        upstream = json.loads(mathlib_text)
    except ValueError as exc:
        return [f"cannot parse a manifest: {exc}"]

    if not SHA_RE.match(mathlib_rev or ""):
        return [f"mathlib rev {mathlib_rev!r} is not a 40-hex commit sha"]

    pr_pkgs = packages_by_name(pr, problems, "the release commit's manifest")
    base_pkgs = packages_by_name(base, problems, "the base manifest")
    up_pkgs = packages_by_name(upstream, problems, "mathlib's manifest")

    if "mathlib" in up_pkgs:
        problems.append("mathlib's own manifest lists a package named 'mathlib'")

    ours = pr_pkgs.get("mathlib")
    theirs = base_pkgs.get("mathlib")
    if ours is None:
        problems.append("the release commit's manifest has no mathlib package")
    elif theirs is None:
        problems.append("the base manifest has no mathlib package")
    else:
        if ours.get("type") != "git":
            problems.append(f"mathlib is pinned as type {ours.get('type')!r}, not git")
        if ours.get("rev") != mathlib_rev:
            problems.append(
                f"mathlib is pinned at {ours.get('rev')!r}, not the release tag commit "
                f"{mathlib_rev}")
        if normalise_url(ours.get("url")) != normalise_url(theirs.get("url")):
            problems.append(
                f"the mathlib url changed from {theirs.get('url')!r} to {ours.get('url')!r}; "
                "swapping the repository is human-owned")
        if ours.get("inputRev") != theirs.get("inputRev"):
            problems.append(
                f"the nominated branch changed from {theirs.get('inputRev')!r} to "
                f"{ours.get('inputRev')!r}; it is human-owned and a release commit never "
                "touches it")

    for name, pkg in sorted(pr_pkgs.items()):
        if pkg.get("type") != "git":
            problems.append(f"package {name!r} is type {pkg.get('type')!r}, not git")
        if not SHA_RE.match(pkg.get("rev") or ""):
            problems.append(f"package {name!r} is not pinned to a 40-hex commit sha")

    extra = sorted(set(pr_pkgs) - set(up_pkgs) - {"mathlib"})
    missing = sorted(set(up_pkgs) - set(pr_pkgs))
    if extra:
        problems.append(f"packages mathlib does not depend on at this revision: {extra}")
    if missing:
        problems.append(f"packages mathlib depends on but the release commit omits: {missing}")
    for name in sorted(set(pr_pkgs) & set(up_pkgs)):
        if identity(pr_pkgs[name]) != identity(up_pkgs[name]):
            problems.append(
                f"package {name!r} is {identity(pr_pkgs[name])}, but mathlib pins "
                f"{identity(up_pkgs[name])}")

    for field in OWN_ROOT_FIELDS:
        if pr.get(field) != base.get(field):
            problems.append(
                f"the root field {field!r} changed from {base.get(field)!r} to "
                f"{pr.get(field)!r}; a release commit only moves the pins")
    return problems


def check_toolchain(pr_text, mathlib_text, release):
    """Problems with a release commit's lean-toolchain, empty when there are none."""
    problems = []
    if not RELEASE_RE.match(release or ""):
        return [f"{release!r} is not a vX.Y.Z[-rcN] release name"]
    want = TOOLCHAIN_PREFIX + release
    pinned = (pr_text or "").strip()
    upstream = (mathlib_text or "").strip()
    if pinned != want:
        problems.append(f"lean-toolchain is {pinned!r}, not {want!r}")
    if upstream != want:
        problems.append(
            f"mathlib's own lean-toolchain at that tag is {upstream!r}, not {want!r}; "
            f"the {release} tag does not name the release it claims to")
    return problems


def read(path):
    with open(path) as handle:
        return handle.read()


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("command", choices=["check"])
    ap.add_argument("--release", required=True)
    ap.add_argument("--rev", required=True, help="mathlib's tag commit for the release")
    ap.add_argument("--pr-manifest", required=True)
    ap.add_argument("--pr-toolchain", required=True)
    ap.add_argument("--base-manifest", required=True)
    ap.add_argument("--mathlib-manifest", required=True)
    ap.add_argument("--mathlib-toolchain", required=True)
    args = ap.parse_args(argv)

    problems = check_toolchain(read(args.pr_toolchain), read(args.mathlib_toolchain),
                               args.release)
    problems += check_manifest(read(args.pr_manifest), read(args.base_manifest),
                               read(args.mathlib_manifest), args.rev)
    for problem in problems:
        print(problem)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
