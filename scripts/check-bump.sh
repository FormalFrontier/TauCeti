#!/usr/bin/env bash
# check-bump.sh — validate that a PR's proposed Lake-pin / toolchain change is a
# safe, machine-checkable *forward* bump, and nothing else.
#
# This is the trust anchor that lets a PR touching `lake-manifest.json` and/or
# `lean-toolchain` be built and auto-merged without a human. The sole lakefile exception is
# `--allow-bot-lakefile`: the trusted review bot may replace Mathlib's nominated branch with the
# immutable first-known-bad SHA (or restore that one field to `master` after the fix), provided
# check_bot_lakefile.py proves that is the only Lake-config change and the manifest agrees.
# the worry is a PR that re-points a dependency at a malicious fork/commit or a
# malicious toolchain and then gets auto-built. We reduce the whole manifest to a
# deterministic function of one validated fact — "mathlib moved forward on the
# branch nominated in lakefile.toml" — and require the toolchain to move forward
# and match mathlib's:
#
#   1. lakefile.toml / lakefile.lean are byte-identical to base, except for the narrow validated
#      review-bot mode above (lakefile.lean is never excepted).
#   2. The nominated require (mathlib) is the ONLY package named "mathlib", is a
#      `git` package pinned to a 40-hex commit SHA, keeps its url, and normally keeps
#      inputRev at `master` (the bot exception may temporarily set inputRev to the exact same SHA,
#      then restore it to `master`).
#      Its new rev is a *descendant of the old rev* AND *on the trusted base
#      inputRev's history* — a genuine forward move on the nominated branch (via
#      the GitHub compare API; the SHA requirement makes the compared revs
#      immutable, so what we validate is exactly what Lake will resolve and build).
#   3. The PR manifest's package set, MINUS mathlib, is EXACTLY mathlib's own
#      lake-manifest at the new rev, field-for-field (type/url/rev/inputRev) — no
#      package added, removed, renamed, retyped (e.g. a `path` dep), duplicated, or
#      re-pointed independently of the trusted mathlib.
#   4. lean-toolchain moves monotonically forward on the leanprover/lean4 channel
#      AND equals mathlib's lean-toolchain at the new rev.
#
# It does NO build and runs NONE of the PR's code — only reads/parses two text
# files and queries the trusted upstream via `gh api`. Usage:
#
#   check-bump.sh <base_dir> <merge_base_dir> <pr_dir> [--allow-bot-lakefile]
#
# where each dir holds the repo's lean-toolchain, lake-manifest.json, lakefile.toml
# (and optionally lakefile.lean). base_dir is the CURRENT target-branch tip — the
# trusted config the PR actually builds and merges against, and what a genuine bump is
# validated against. merge_base_dir is the PR's merge-base with the target branch, used
# only to decide whether the PR changed these files at all (so a PR that is merely
# behind the tip is not judged as if it had edited them). Exit 0 = safe forward bump
# (or no pin change); exit 1 = not auto-mergeable (route to a human). Reasons printed.
set -uo pipefail

BASE="${1:?usage: check-bump.sh <base_dir> <merge_base_dir> <pr_dir>}"
MERGE_BASE="${2:?usage: check-bump.sh <base_dir> <merge_base_dir> <pr_dir>}"
PR="${3:?usage: check-bump.sh <base_dir> <merge_base_dir> <pr_dir>}"
MODE="${4:-}"
[ -z "$MODE" ] || [ "$MODE" = "--allow-bot-lakefile" ] \
  || { echo "usage: check-bump.sh <base_dir> <merge_base_dir> <pr_dir> [--allow-bot-lakefile]"; exit 2; }

fail() { echo "::error::bump-guard: $*"; echo "BUMP-GUARD: FAIL — $*"; exit 1; }
ok()   { echo "BUMP-GUARD: PASS — $*"; exit 0; }

# --- 0. is this a pin change at all? (the PR's OWN delta, vs its merge-base) ---
# Validate only what the PR itself changes in the human-owned lakefile and the Lake
# pins. If none of these differ from the merge-base, the PR did not touch them — it is
# not a bump (it may merely be behind the target tip, which has moved them forward
# underneath it), so pass trivially. Only when the PR's own delta touches one of them
# do we judge it, strictly, against the CURRENT base config (steps 1–4 below). This is
# the one fact that needs the merge-base; everything below is relative to BASE (tip).
pin_changed=0
for f in lakefile.toml lakefile.lean lake-manifest.json lean-toolchain; do
  m="$MERGE_BASE/$f"; p="$PR/$f"
  [ -f "$m" ] || m=/dev/null
  [ -f "$p" ] || p=/dev/null
  if ! diff -q "$m" "$p" >/dev/null 2>&1; then pin_changed=1; break; fi
done
[ "$pin_changed" = 0 ] && ok "no lakefile or Lake-pin change relative to the merge-base"

# --- 1. lakefile is human-owned; validate the one trusted-bot exception -------
f=lakefile.lean
b="$BASE/$f"; p="$PR/$f"
# Treat an absent file the same on both sides; a file appearing/vanishing is a change.
[ -f "$b" ] || b=/dev/null
[ -f "$p" ] || p=/dev/null
if ! diff -q "$b" "$p" >/dev/null 2>&1; then
  fail "$f differs from base — lakefile edits are human-owned and never auto-merge"
fi
if [ "$MODE" = "--allow-bot-lakefile" ]; then
  python3 "$BASE/scripts/check_bot_lakefile.py" \
    "$BASE/lakefile.toml" "$PR/lakefile.toml" "$PR/lake-manifest.json" \
    || fail "review-bot lakefile pin is not the exact validated Mathlib revision change"
else
  b="$BASE/lakefile.toml"; p="$PR/lakefile.toml"
  [ -f "$b" ] || b=/dev/null
  [ -f "$p" ] || p=/dev/null
  if ! diff -q "$b" "$p" >/dev/null 2>&1; then
    fail "lakefile.toml differs from base — only the trusted review bot's exact Mathlib pin may auto-merge"
  fi
fi

# --- helpers ------------------------------------------------------------------
# owner/repo slug from a github url
slug() { sed -E 's#^https?://github.com/##; s#/$##; s#\.git$##' <<<"$1"; }

# Print "url<TAB>rev<TAB>inputRev" for THE mathlib package in <file>, after asserting:
# exactly one package named mathlib, of type git, with a 40-hex commit-SHA rev. Any
# violation prints "ERROR: ..." and exits 1 (so the caller can `|| fail`).
mathlib_of() {
  python3 - "$1" <<'PY'
import json,sys,re
try:
    m=json.load(open(sys.argv[1]))
except Exception as e:
    print(f"ERROR: cannot parse manifest: {e}"); sys.exit(1)
pkgs=m.get("packages",[])
names=[p.get("name") for p in pkgs]
dups=sorted({n for n in names if names.count(n)>1})
if dups: print(f"ERROR: duplicate package names in manifest: {dups}"); sys.exit(1)
ml=[p for p in pkgs if p.get("name")=="mathlib"]
if len(ml)!=1: print(f"ERROR: expected exactly one 'mathlib' package, found {len(ml)}"); sys.exit(1)
p=ml[0]
if p.get("type")!="git": print(f"ERROR: mathlib package is not type git (got {p.get('type')!r})"); sys.exit(1)
rev=p.get("rev") or ""
if not re.fullmatch(r"[0-9a-f]{40}", rev): print(f"ERROR: mathlib rev {rev!r} is not a 40-hex commit SHA"); sys.exit(1)
url=(p.get("url") or "").rstrip("/")
if url.endswith(".git"): url=url[:-4]
print("\t".join([url, rev, p.get("inputRev") or ""]))
PY
}

ml_base="$(mathlib_of "$BASE/lake-manifest.json")" || fail "base manifest: ${ml_base#ERROR: }"
ml_pr="$(mathlib_of   "$PR/lake-manifest.json")"   || fail "PR manifest: ${ml_pr#ERROR: }"
IFS=$'\t' read -r ML_URL_B ML_REV_B ML_IR_B <<<"$ml_base"
IFS=$'\t' read -r ML_URL_P ML_REV_P ML_IR_P <<<"$ml_pr"

[ "$ML_URL_B" = "$ML_URL_P" ] || fail "mathlib url changed ($ML_URL_B -> $ML_URL_P) — repo swap is human-owned"
if [ "$MODE" = "--allow-bot-lakefile" ]; then
  if [ "$ML_IR_P" = "$ML_REV_P" ]; then
    [ "$ML_IR_B" = "master" ] \
      || fail "an exact review-bot pin may only start from the trusted master nomination (base inputRev=$ML_IR_B)"
    NOMINATED_BRANCH="$ML_IR_B"
  elif [ "$ML_IR_P" = "master" ]; then
    [ "$ML_IR_B" = "$ML_REV_B" ] \
      || fail "review-bot de-pin to master requires an exact pinned base ($ML_IR_B != $ML_REV_B)"
    NOMINATED_BRANCH="$ML_IR_P"
  else
    fail "review-bot manifest inputRev must be its exact Mathlib rev or master (got $ML_IR_P)"
  fi
else
  [ "$ML_IR_B" = "$ML_IR_P" ] \
    || fail "mathlib inputRev (nominated branch) changed ($ML_IR_B -> $ML_IR_P) — human-owned"
  NOMINATED_BRANCH="$ML_IR_B"
fi
ML_SLUG="$(slug "$ML_URL_P")"

# --- 2. mathlib moved forward on the nominated branch -------------------------
if [ "$ML_REV_B" = "$ML_REV_P" ]; then
  # mathlib pin unchanged: then NOTHING in the manifest may change (the rest is derived from it).
  if ! diff -q "$BASE/lake-manifest.json" "$PR/lake-manifest.json" >/dev/null 2>&1; then
    fail "mathlib rev unchanged but the manifest changed — not a derived bump"
  fi
  echo "bump-guard: mathlib pin unchanged."
else
  st_fwd="$(gh api "repos/$ML_SLUG/compare/$ML_REV_B...$ML_REV_P" --jq '.status' 2>/dev/null)" \
    || fail "compare API failed for $ML_SLUG $ML_REV_B...$ML_REV_P"
  case "$st_fwd" in
    ahead) : ;;  # new strictly descends from old — forward
    *) fail "mathlib rev is not a forward move from base (compare status: ${st_fwd:-unknown}); old=$ML_REV_B new=$ML_REV_P" ;;
  esac
  # Membership is checked against the trusted branch: normally the base nomination; `master` from
  # the bot PR itself only when it is undoing an exact-SHA base nomination.
  st_branch="$(gh api "repos/$ML_SLUG/compare/$ML_REV_P...$NOMINATED_BRANCH" --jq '.status' 2>/dev/null)" \
    || fail "compare API failed for $ML_SLUG $ML_REV_P...$NOMINATED_BRANCH"
  case "$st_branch" in
    ahead|identical) : ;;  # the nominated branch tip is at-or-ahead of new — new is on its history
    *) fail "mathlib new rev $ML_REV_P is not on branch '$NOMINATED_BRANCH' (compare status: ${st_branch:-unknown})" ;;
  esac
  echo "bump-guard: mathlib $ML_REV_B -> $ML_REV_P is a forward move on '$NOMINATED_BRANCH'."
fi

# --- 3. the rest of the manifest is EXACTLY mathlib's own manifest at the new rev
ML_MANIFEST="$(gh api "repos/$ML_SLUG/contents/lake-manifest.json?ref=$ML_REV_P" --jq '.content' 2>/dev/null | base64 -d)" \
  || fail "cannot fetch mathlib lake-manifest.json at $ML_REV_P"
ML_TMP="$(mktemp)"; trap 'rm -f "$ML_TMP"' EXIT
printf '%s' "$ML_MANIFEST" > "$ML_TMP"

derived_msg="$(python3 - "$PR/lake-manifest.json" "$ML_TMP" <<'PY'
import json,sys,re
def norm_url(u):
    u=(u or "").rstrip("/")
    return u[:-4] if u.endswith(".git") else u
def load(p):
    return json.load(open(p)).get("packages",[])
pr, ml = load(sys.argv[1]), load(sys.argv[2])

def tup(p):  # the identity we require to match, field-for-field
    return (p.get("type"), norm_url(p.get("url")), p.get("rev"), p.get("inputRev"))

# PR manifest: no dup names, every package is git pinned to a 40-hex SHA.
prnames=[p.get("name") for p in pr]
dups=sorted({n for n in prnames if prnames.count(n)>1})
if dups: print(f"duplicate package names in PR manifest: {dups}"); sys.exit(1)
for p in pr:
    if p.get("type")!="git":
        print(f"PR pins non-git package '{p.get('name')}' (type {p.get('type')!r}); only git deps derived from mathlib are allowed"); sys.exit(1)
    if not re.fullmatch(r"[0-9a-f]{40}", p.get("rev") or ""):
        print(f"PR dep '{p.get('name')}' rev is not a 40-hex commit SHA"); sys.exit(1)

# The PR's deps, minus mathlib, must be EXACTLY mathlib's own deps — same names, same fields.
pr_by  = {p.get("name"): p for p in pr if p.get("name")!="mathlib"}
ml_by  = {p.get("name"): p for p in ml}
only_pr = sorted(set(pr_by) - set(ml_by))
only_ml = sorted(set(ml_by) - set(pr_by))
if only_pr: print(f"PR pins deps mathlib@new does not depend on: {only_pr}"); sys.exit(1)
if only_ml: print(f"PR is missing deps mathlib@new depends on: {only_ml}"); sys.exit(1)
for n in pr_by:
    if tup(pr_by[n]) != tup(ml_by[n]):
        print(f"dep '{n}' does not match mathlib@new (PR {tup(pr_by[n])} vs mathlib {tup(ml_by[n])})"); sys.exit(1)
print("OK")
PY
)" || fail "${derived_msg:-transitive pins do not match mathlib@$ML_REV_P}"
echo "bump-guard: all transitive pins match mathlib@$ML_REV_P exactly."

# --- 4. toolchain: monotonic forward AND consistent with mathlib --------------
TC_B="$(tr -d '[:space:]' <"$BASE/lean-toolchain" 2>/dev/null)"
TC_P="$(tr -d '[:space:]' <"$PR/lean-toolchain" 2>/dev/null)"
[ -n "$TC_B" ] || fail "cannot read base lean-toolchain"
[ -n "$TC_P" ] || fail "cannot read PR lean-toolchain"

if [ "$TC_B" != "$TC_P" ]; then
  tc_msg="$(python3 - "$TC_B" "$TC_P" <<'PY'
import re,sys
def parse(t):
    m=re.fullmatch(r"leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?", t)
    if not m: print(f"toolchain '{t}' is not a leanprover/lean4 vX.Y.Z[-rcN] release"); sys.exit(1)
    x,y,z,rc=m.groups()
    return (int(x),int(y),int(z), int(rc) if rc is not None else float("inf"))  # release > any rc of same X.Y.Z
b,p=parse(sys.argv[1]),parse(sys.argv[2])
if p < b: print(f"toolchain moved backward ({sys.argv[1]} -> {sys.argv[2]})"); sys.exit(1)
PY
  )" || fail "${tc_msg:-toolchain is not a monotonic forward release}"
fi

ML_TC="$(gh api "repos/$ML_SLUG/contents/lean-toolchain?ref=$ML_REV_P" --jq '.content' 2>/dev/null | base64 -d | tr -d '[:space:]')" \
  || fail "cannot fetch mathlib lean-toolchain at $ML_REV_P"
[ "$TC_P" = "$ML_TC" ] || fail "PR lean-toolchain ($TC_P) != mathlib@$ML_REV_P's ($ML_TC)"
echo "bump-guard: toolchain $TC_B -> $TC_P is forward and matches mathlib@$ML_REV_P."

ok "forward-only bump validated (mathlib on '$NOMINATED_BRANCH', derived transitive pins, toolchain consistent)"
