#!/usr/bin/env bash
# check-release-commit.sh -- decide whether a commit may be built, published and tagged
# as Tau Ceti's release commit for a Lean release.
#
# This is the trust anchor of .github/workflows/release-tag.yml. That workflow builds
# the target commit UNSANDBOXED and publishes the resulting oleans into the Lake cache
# every pr-build restores from, so something has to establish that running the target
# is no more dangerous than running main, which ci.yml already does on every push.
# That is what this script establishes, and it does it in the trusted resolve job, from
# main's copy of this file, without ever placing the target's tree on disk.
#
# The property, by kind of target:
#
#   main-commit     The target is an ancestor of main. There is nothing to prove about
#                   its tree: it IS main, already reviewed, merged through bump-guard
#                   and built by ci.yml. All that remains is that it names the release
#                   it claims to: the right toolchain, and either mathlib's own tag
#                   commit (exact) or a master descendant of it (inexact).
#
#   release-branch  The target is ONE commit on releases/<release>, its parent is an
#                   ancestor of main, and it changes only lake-manifest.json and
#                   lean-toolchain. Those two files are declarative, are not code, and
#                   are a deterministic function of one externally verified fact:
#                   mathlib's own tag, and mathlib's own manifest and toolchain at it.
#                   So the target is exactly as trustworthy as the main commit it
#                   derives from. This is strictly stronger than scripts/check-bump.sh,
#                   which permits a forward move to an unreviewed master commit; here
#                   the pin has no freedom at all.
#
# It runs NO build and executes nothing from the target: it reads two text files
# through the API and queries the trusted upstream with `gh api`. Usage:
#
#   check-release-commit.sh <release> <sha> <exact:true|false>
#
# Exit 0 and emit sha/release/toolchain/mathlib-rev/kind/exact to $GITHUB_OUTPUT when
# the target is a valid release commit; exit 1 with the reason otherwise.
set -uo pipefail

RELEASE="${1:?usage: check-release-commit.sh <release> <sha> <exact>}"
SHA="${2:?usage: check-release-commit.sh <release> <sha> <exact>}"
EXACT="${3:?usage: check-release-commit.sh <release> <sha> <exact>}"

REPO="${GH_REPO:-TauCetiProject/TauCeti}"
MATHLIB="${MATHLIB_REPO:-leanprover-community/mathlib4}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

fail() { echo "::error::release-commit: $*"; echo "RELEASE-COMMIT: FAIL -- $*"; exit 1; }
note() { echo "release-commit: $*"; }

emit() { [ -n "${GITHUB_OUTPUT:-}" ] && printf '%s\n' "$1" >> "$GITHUB_OUTPUT"; return 0; }

# --- 0. the inputs are attacker-chosen: validate before they key anything ------
# Both reach an API path, a file name and a command line below. pr-labels.yml makes
# the same point about its own input and validates it down to digits first.
[[ "$RELEASE" =~ ^v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$ ]] \
  || fail "release '$RELEASE' is not a vX.Y.Z[-rcN] name"
[[ "$SHA" =~ ^[0-9a-f]{40}$ ]] || fail "sha '$SHA' is not a 40-hex commit id"
case "$EXACT" in true|false) ;; *) fail "exact must be true or false, got '$EXACT'" ;; esac

WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT

# Read a file from a repository at a revision. Never a checkout: the target's tree must
# not be placed on disk in a trusted job, and keying on the immutable sha means a force
# push to the release branch cannot race this check.
contents() { # contents <repo> <path> <ref> <outfile>
  gh api "repos/$1/contents/$2?ref=$3" --jq '.content' 2>/dev/null | base64 -d > "$4"
}

# --- 1. the commit exists in THIS repository ----------------------------------
got="$(gh api "repos/$REPO/commits/$SHA" --jq '.sha' 2>/dev/null)" \
  || fail "commit $SHA is not in $REPO"
[ "$got" = "$SHA" ] || fail "$REPO resolved $SHA to $got"

# --- 2. anchor the target to main ---------------------------------------------
cmp_json="$WORK/compare.json"
gh api "repos/$REPO/compare/main...$SHA" > "$cmp_json" 2>/dev/null \
  || fail "compare API failed for $REPO main...$SHA"
status="$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["status"])' "$cmp_json")"

case "$status" in
  identical|behind)
    KIND="main-commit"
    note "$SHA is an ancestor of main ($status)"
    ;;
  diverged)
    KIND="release-branch"
    [ "$EXACT" = "true" ] \
      || fail "a release branch carries the exact pin; the inexact rung is only ever a main commit"
    branch="releases/$RELEASE"
    head="$(gh api "repos/$REPO/git/ref/heads/$branch" --jq '.object.sha' 2>/dev/null)" \
      || fail "no branch $branch, so $SHA is not on main and is not this release's branch"
    [ "$head" = "$SHA" ] || fail "$branch is at $head, not $SHA"
    # `ahead_by == 1` alone does not exclude a merge commit, so require one parent, and
    # require that parent to be an ancestor of main rather than merely reachable.
    ahead="$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["ahead_by"])' "$cmp_json")"
    [ "$ahead" = "1" ] || fail "$SHA is $ahead commits ahead of main; a release commit is exactly one"
    parents="$(gh api "repos/$REPO/git/commits/$SHA" --jq '[.parents[].sha] | join(" ")')" \
      || fail "cannot read the parents of $SHA"
    set -- $parents
    [ "$#" = "1" ] || fail "$SHA has $# parents; a release commit has exactly one"
    PARENT="$1"
    pstatus="$(gh api "repos/$REPO/compare/$PARENT...main" --jq '.status' 2>/dev/null)" \
      || fail "compare API failed for $REPO $PARENT...main"
    case "$pstatus" in
      ahead|identical) : ;;
      *) fail "the parent $PARENT of $SHA is not an ancestor of main (compare: $pstatus)" ;;
    esac
    # The diff must be the two pin files and nothing else. The compare endpoint caps
    # `.files` at 300, and a truncated list could hide an out-of-scope path, so a
    # release commit that somehow reached that cap is refused rather than trusted.
    python3 - "$cmp_json" <<'PY' || fail "the release commit changes more than the two Lake pins"
import json, sys
allowed = {"lake-manifest.json", "lean-toolchain"}
files = json.load(open(sys.argv[1])).get("files", [])
if not files or len(files) > 2 or len(files) >= 300:
    print(f"::error::release-commit: {len(files)} changed files, expected 1 or 2")
    sys.exit(1)
bad = [f for f in files
       if f.get("filename") not in allowed or f.get("status") != "modified"]
if bad:
    for f in bad:
        print(f"::error::release-commit: {f.get('filename')!r} ({f.get('status')}) is "
              "outside the two Lake pins")
    sys.exit(1)
PY
    note "$SHA is one pin-only commit on $branch, off $PARENT on main"
    ;;
  *)
    fail "$SHA is neither an ancestor of main nor a release branch (compare: $status)"
    ;;
esac

# --- 3. mathlib's own tag for this release ------------------------------------
read -r obj kind < <(gh api "repos/$MATHLIB/git/ref/tags/$RELEASE" \
  --jq '[.object.sha, .object.type] | @tsv' 2>/dev/null | tr '\t' ' ') \
  || fail "$MATHLIB has no tag $RELEASE"
if [ "$kind" = "tag" ]; then
  obj="$(gh api "repos/$MATHLIB/git/tags/$obj" --jq '.object.sha')" \
    || fail "cannot peel the annotated tag $RELEASE"
fi
M="$obj"
[[ "$M" =~ ^[0-9a-f]{40}$ ]] || fail "$MATHLIB tag $RELEASE resolved to '$M'"
note "$MATHLIB $RELEASE is $M"

# --- 4. the target's own pins -------------------------------------------------
contents "$REPO" "lean-toolchain" "$SHA" "$WORK/pr-toolchain" \
  || fail "cannot read lean-toolchain at $SHA"
contents "$REPO" "lake-manifest.json" "$SHA" "$WORK/pr-manifest" \
  || fail "cannot read lake-manifest.json at $SHA"
contents "$MATHLIB" "lean-toolchain" "$M" "$WORK/ml-toolchain" \
  || fail "cannot read mathlib's lean-toolchain at $M"
contents "$MATHLIB" "lake-manifest.json" "$M" "$WORK/ml-manifest" \
  || fail "cannot read mathlib's lake-manifest.json at $M"

TOOLCHAIN="$(tr -d '\n' < "$WORK/pr-toolchain")"
PINNED="$(python3 -c '
import json,sys
pkgs=[p for p in json.load(open(sys.argv[1]))["packages"] if p.get("name")=="mathlib"]
print(pkgs[0]["rev"] if len(pkgs)==1 else "")' "$WORK/pr-manifest")"
[ -n "$PINNED" ] || fail "the target's manifest does not pin exactly one mathlib package"

if [ "$KIND" = "release-branch" ]; then
  # Full derivation check against the base the branch actually came off.
  contents "$REPO" "lake-manifest.json" "$PARENT" "$WORK/base-manifest" \
    || fail "cannot read lake-manifest.json at the base $PARENT"
  python3 "$HERE/release_commit.py" check \
    --release "$RELEASE" --rev "$M" \
    --pr-manifest "$WORK/pr-manifest" --pr-toolchain "$WORK/pr-toolchain" \
    --base-manifest "$WORK/base-manifest" \
    --mathlib-manifest "$WORK/ml-manifest" --mathlib-toolchain "$WORK/ml-toolchain" \
    || fail "the release commit's pins are not mathlib's own at $RELEASE (see above)"
else
  # A main commit is already trusted; all that is in question is which release it names.
  want="leanprover/lean4:$RELEASE"
  [ "$TOOLCHAIN" = "$want" ] || fail "$SHA is on '$TOOLCHAIN', not '$want'"
  upstream="$(tr -d '\n' < "$WORK/ml-toolchain")"
  [ "$upstream" = "$want" ] \
    || fail "mathlib's lean-toolchain at $RELEASE is '$upstream', so that tag does not name it"
  if [ "$EXACT" = "true" ]; then
    [ "$PINNED" = "$M" ] || fail "an exact tag pins $M; $SHA pins $PINNED"
  else
    st="$(gh api "repos/$MATHLIB/compare/$M...$PINNED" --jq '.status' 2>/dev/null)" \
      || fail "compare API failed for $MATHLIB $M...$PINNED"
    case "$st" in
      ahead) : ;;  # the pin strictly descends from the release tag
      *) fail "an inexact tag's pin must descend from $RELEASE; $PINNED compares '$st'" ;;
    esac
  fi
fi

# --- 5. the target can actually be published ----------------------------------
# Lake scopes an upload by repository, toolchain and platform, and leaves the platform
# out only for a package declaring `platformIndependent = true`. The publish job passes
# `--repo` and `--toolchain` and deliberately no `--platform`, so a target whose lakefile
# predates that declaration would be published under a scope no consumer ever reads.
# The staging step catches it too, but only after a 50 minute build; catch it here.
# TauCeti gained the declaration on 2026-07-27, so every release older than that needs a
# platform-scoped publish before it can be tagged. See docs/toolchain-tags.md.
contents "$REPO" "lakefile.toml" "$SHA" "$WORK/lakefile" \
  || fail "cannot read lakefile.toml at $SHA"
if grep -Eq '^[[:space:]]*platformIndependent[[:space:]]*=[[:space:]]*true' "$WORK/lakefile"; then
  PLATFORM_INDEPENDENT=true
else
  # TauCeti only declared `platformIndependent` on 2026-07-27, and every release older
  # than that is platform-scoped. That is publishable, it just has to be published under
  # the scope such a consumer reads: `<repo>/pt/<triple>/tc/<toolchain>/<rev>`.
  PLATFORM_INDEPENDENT=false
  note "the lakefile at $SHA does not declare platformIndependent; this release publishes under a platform-scoped key"
fi
if grep -Eq '^[[:space:]]*(fixedToolchain|bootstrap)[[:space:]]*=[[:space:]]*true' "$WORK/lakefile"; then
  fail "the lakefile at $SHA sets fixedToolchain or bootstrap, so Lake drops the toolchain from the upload scope while the publish job supplies one"
fi

# --- 6. never move a published tag --------------------------------------------
# Checked here, at minute two, rather than after a 55 minute build.
existing="$(gh api "repos/$REPO/git/ref/tags/$RELEASE" \
  --jq '[.object.sha, .object.type] | @tsv' 2>/dev/null | tr '\t' ' ')" || existing=""
if [ -n "$existing" ]; then
  set -- $existing
  tagged="$1"
  if [ "${2:-}" = "tag" ]; then
    tagged="$(gh api "repos/$REPO/git/tags/$tagged" --jq '.object.sha')"
  fi
  [ "$tagged" = "$SHA" ] \
    || fail "$RELEASE already tags $tagged; a published tag is never moved"
  note "$RELEASE already tags $SHA; the tag job will report it and do nothing"
fi

emit "sha=$SHA"
emit "release=$RELEASE"
emit "toolchain=$TOOLCHAIN"
emit "mathlib-rev=$M"
emit "kind=$KIND"
emit "exact=$EXACT"
emit "platform-independent=$PLATFORM_INDEPENDENT"
echo "RELEASE-COMMIT: PASS -- $SHA is Tau Ceti's $RELEASE release commit ($KIND, exact=$EXACT)"
