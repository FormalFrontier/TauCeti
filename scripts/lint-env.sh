#!/usr/bin/env bash
# lint-env.sh — enforce Mathlib's default environment-linter set (`#lint`) plus a
# reliable docstring check, with a grandfathered baseline. This generalizes the former
# lint-simp-nf.sh from `#lint only simpNF` to all default linters (simpNF, checkType,
# synTaut, structureInType, defsWithUnderscore, simpComm, ...).
#
# Why not `lake exe runLinter TauCeti`: the root TauCeti.lean is intentionally empty
# (the lakefile glob is authoritative for what gets built), so runLinter would lint an
# empty environment and pass vacuously. Instead we generate a driver module that
# imports every `TauCeti/**/*.lean` module and runs `#lint only ... in TauCeti`,
# elaborate it against the already-built oleans (`lake env lean`), and parse the
# violations out of the linter report, attributing each one to the linter whose
# section it appears in.
#
# docBlame IS EXCLUDED from the `#lint` pass and replaced by a direct scan — do NOT
# "simplify" this back to the linter. Under the Lean module system the linter
# framework's introspection is systematically wrong across module boundaries:
#   * docstrings are exported only to the `server`/`private` parts of the `.olean`
#     (see `docStringExt` in Lean's `DocString/Extension.lean`: `exported := #[]`),
#     so in the module-style driver `Lean.findDocString?` sees NO docstring for any
#     imported declaration and docBlame flags thousands of documented declarations;
#   * theorems whose proofs live in non-`@[expose]`d oleans are surfaced to it as
#     `axiom`s (docBlame reported ~4.5k phantom "axiom missing documentation string"
#     hits, and misclassified undocumented defs as axioms, on a library with zero
#     real axioms — CI's `lake exe axioms` audit proves that separately).
# `#lint` has no exclusion syntax, so the driver runs `#lint only $LINTERS`, the
# explicit default-set-minus-docBlame list below. Running docBlame and dropping its
# report section instead would open a forgery channel (a crafted declaration name
# containing a newline could print a fake `docBlame` section opener inside the report
# and swallow subsequent real violations); with `only`, docBlame never runs, so any
# docBlame-attributed line is a forgery and fails closed as an unbaselined violation.
# So that new default linters added upstream are not silently missed, the docstring
# scan driver re-derives the default set from the environment and FAILS if it no
# longer equals $LINTERS + docBlame — a Batteries/Mathlib bump that changes the
# default linter set turns into a loud CI failure asking for a human update here.
# The docstring check itself runs as a
# generated LEGACY (non-module) driver with plain imports: with a non-module root,
# Lean imports the whole closure at the `private` olean level, where both docstrings
# and true declaration kinds are visible. Calibration (2026-07, this file's PR):
# module-style probes (`public import` and `import all`) both returned no docstring
# for known-documented declarations, the legacy probe found 671/677 documented,
# flagged a scratch undocumented `def` by name, and did not flag known-documented
# `TauCeti.GridDiagram.OSet`, `TauCeti.Isotopy`,
# `TauCeti.AlgebraicGeometry.WeilDivisor.coeff`. Standing fail-closed guards (each
# with a distinct failure message, so a regression is diagnosable):
#   * the scan echoes every scanned declaration as a `DOCSCAN-ALL <decl> <status>`
#     line (tallies cross-checked against the nonce-protected summary);
#   * the three known-documented sentinel declarations above, spread across the
#     library, must each be scanned AND seen as documented (full blindness sees no
#     docstrings; PARTIAL blindness would silently narrow coverage);
#   * every `docString` baseline entry must still appear among the scanned
#     declarations — no longer VIOLATING is ratchetable, but no longer SCANNED is
#     coverage loss and fails;
#   * a minimum scanned-count floor (500; see the inline comment) catches a
#     collapsed candidate set.
# If docstring storage or the candidate enumeration moves again, these checks FAIL
# rather than reporting hundreds of false violations or silently passing. The scan mirrors
# docBlame's rules (skip auto-generated declarations, instances, `Prop`-valued
# projections; require docstrings on definitions, inductives, opaques, axioms —
# theorems are deliberately exempt, as in Mathlib, where docBlameThm is a separate,
# non-default linter). Its findings are reported under the pseudo-linter name
# `docString`. NOTE: `@[nolint docBlame]` has no effect on the scan (it does not read
# nolint attributes); deliberate exceptions get a `docString <decl>` baseline entry.
#
# Violations that predate this check are grandfathered in scripts/lint-baseline.txt
# (lines of `<linter> <declName>`, LC_ALL=C sorted, no duplicates):
#   - a (linter, declaration) pair NOT in the baseline is a NEW violation  -> exit 1;
#   - a baseline entry that no longer violates is printed as a RATCHET reminder
#     (delete it from the baseline in a follow-up PR), without failing.
# The simpNF entries are the deliberate exception set kept after the 2026-07
# library-wide cleanup (see the wave-2/3 PR bodies, TauCeti #649-#657, #669-#673, for
# per-entry rationale); the rest are grandfathered singletons being fixed in parallel
# PRs.
#
# LINTER FAILED entries: a linter can crash on a declaration instead of judging it
# (its `#check` block then reads `/- LINTER FAILED: ... -/`; e.g. structureInType
# currently crashes on a private structure — another module-system introspection
# artifact). We treat a crash as a violation attributed to that linter, baseline-able
# like any other, so the known artifacts are grandfathered but a linter crashing on
# NEW code fails CI loudly rather than silently skipping the declaration.
#
# `@[nolint <linter>]` ratchet: silencing a linter per-declaration would bypass the
# baseline, so every `@[nolint ...]` application under TauCeti/ must be accounted for
# in scripts/lint-nolints-allowlist.txt as a DECLARATION-LEVEL `<linter> <declName>`
# line (LC_ALL=C sorted, no duplicates — the same shape as the baseline). The pairs
# are derived from the environment, not from source text: the docstring-scan driver
# enumerates the persistent `nolint` attribute entries of every TauCeti module (a
# parametric attribute can only be applied in its target's defining module, so this
# is exhaustive for anything that could silence the `#lint` driver; multi-target
# `attribute [nolint foo] a b` and multi-linter `@[nolint simpComm simpNF]` forms
# yield one pair per (linter, target)). Occurrence COUNTS would fail open here:
# broadening an allowlisted `attribute [nolint foo] a` to `a b c` keeps any per-file
# count intact, but adds (foo, b) and (foo, c) pairs that are not allowlisted -> fail.
# The enumeration is calibrated per run: it must see at least one nolint entry among
# ALL imported modules (Batteries/Mathlib carry some), else it fails as blind.
# Growing the allowlist must go through the same human-reviewed path as this script —
# it is exactly the hole an auto-merged PR would otherwise use.
#
# SECURITY MODEL (this script elaborates the PR's own code — both drivers execute
# import-time initializers — so treat all lean output as partially
# attacker-controlled):
#   * The `#lint` report starts with a header line
#       -- Found N error(s) in M declarations (plus ...) in TauCeti with K linters
#     followed (when N > 0) by one section per reporting linter, opened by a line
#       /- The `<linter>` linter reports:
#     and containing one `#check <decl> /- ... -/` block per violation.
#     When N > 0 the report is an error diagnostic, so the header carries the
#     `<driver>:<line>:<col>: error: ` prefix of our own driver file (a fresh mktemp
#     path) and lean exits nonzero; when N = 0 it is an info message printed bare.
#     We require EXACTLY ONE header in the output, of the form matching the exit
#     code (anchored error header + N > 0 for a nonzero exit; bare header + N = 0
#     for a zero exit), and we require the header's "with K linters" to equal the
#     length of the `#lint only` list we requested.
#   * The report region (everything after the header) is parsed by a block-aware
#     state machine: a `#check` block runs from `^#check ` to the first line ending
#     in `-/`, and everything inside it is comment CONTENT (violation messages embed
#     attacker-chosen declaration names and types, so a message line shaped like a
#     section opener or a `#check` must not carry structure). Section openers are
#     accepted only OUTSIDE blocks, must name a linter from the expected set
#     (docBlame never runs, so a docBlame opener is forgery by construction), and no
#     section may open twice — otherwise forged content could re-attribute
#     subsequent real `#check`s to another linter, and a declaration can
#     legitimately sit under two linters in the baseline. Each block must close
#     before the next opens and must fall inside a section, and the block count must
#     equal N. Every grammar violation is a DISTINCT driver failure, never a pass.
#   * PR code can print arbitrary text at import time (initializers): a forged header
#     printed alongside the real one yields two headers -> fail, and a forged smaller
#     report cannot suppress the real report's `error:` diagnostic or lean's nonzero
#     exit. Forged `#check` lines make the block count disagree with N -> fail.
#   * The docstring scan prints one `DOCSCAN <decl> ...` line per violation, one
#     `DOCSCAN-ALL <decl> <status>` line per scanned declaration, one
#     `NOLINT <linter> <decl>` line per TauCeti `@[nolint]` application, and exactly
#     one summary line ending in a per-run random nonce marker, carrying its own
#     counts for ALL of these. We require exit 0, EXACTLY ONE summary line, every
#     count to match its line tally, the calibration guards above (sentinels,
#     baseline coverage, scanned floor, at least one visible docstring), and the
#     nolint pairs to be allowlisted. Forged DOCSCAN/DOCSCAN-ALL/NOLINT lines break
#     the tallies (they can only ADD lines — the real ones still print); a forged
#     summary must predict the nonce.
#   * The remaining forgery needs a process to die before the real work runs while
#     having already printed a single self-consistent PASSING report. Commands after
#     a failed command still elaborate, so the `#lint` driver appends a `#eval`
#     printing a per-run random nonce after the `#lint`, and we require that marker
#     AFTER the header; the scan's nonce-carrying summary plays the same role there.
#   * Residual risk (accepted): initializer code could read /proc/self/cmdline to
#     learn the driver path AND read the driver file to learn the nonce, then forge a
#     passing report and exit(0) before the real work. Any lint that elaborates
#     untrusted code has this ceiling; the pr-build landrun sandbox plus human review
#     of suspicious `initialize`/`@[init]` code are the outer defense. Everything
#     short of that deliberate two-step forgery fails closed.
#
# Run from the repo root (or anywhere; it cd's to the root) AFTER `lake build` — it
# needs the compiled oleans. It does no network I/O and writes only under $TMPDIR, so
# it is safe inside the pr-build landrun sandbox. Usage:
#
#   scripts/lint-env.sh            # check against the baseline
#   scripts/lint-env.sh --update   # rewrite the baseline from the current state
set -euo pipefail

cd "$(dirname "$0")/.."
BASELINE="scripts/lint-baseline.txt"
ALLOWLIST="scripts/lint-nolints-allowlist.txt"
UPDATE=0
[ "${1:-}" = "--update" ] && UPDATE=1

fail() { echo "::error::lint-env: $*"; echo "LINT-ENV: FAIL — $*"; exit 1; }

TMP="$(mktemp -d)" || fail "mktemp failed"
trap 'rm -rf "$TMP"' EXIT
DRIVER="$TMP/LintEnvDriver.lean"
DOCDRIVER="$TMP/DocScanDriver.lean"

# --- 0. `@[nolint <linter>]` ratchet: validate the allowlist shape up front -------
# The authoritative check is declaration-level and environment-derived (see step 1b):
# the docstring-scan driver enumerates every persistent `@[nolint ...]` entry
# originating from a TauCeti module as a `<linter> <declName>` pair, and each pair
# must appear verbatim in $ALLOWLIST (LC_ALL=C sorted, no duplicates — the same shape
# as the baseline). Occurrence COUNTS are not enough: broadening an existing
# `attribute [nolint foo] a` to `a b c` would keep a per-file count unchanged.
[ -f "$ALLOWLIST" ] || fail "allowlist $ALLOWLIST not found — it must be checked in (empty is fine)"
LC_ALL=C sort -cu "$ALLOWLIST" 2>/dev/null \
  || fail "$ALLOWLIST is not sorted/duplicate-free — fix it with: LC_ALL=C sort -u -o $ALLOWLIST $ALLOWLIST"

# --- 0b. validate the baseline before spending minutes on elaboration ------------
if [ "$UPDATE" != 1 ]; then
  [ -f "$BASELINE" ] || fail "baseline $BASELINE not found — run scripts/lint-env.sh --update to create it"
  LC_ALL=C sort -cu "$BASELINE" 2>/dev/null \
    || fail "$BASELINE is not sorted/duplicate-free — fix it with: LC_ALL=C sort -u -o $BASELINE $BASELINE"
fi

NONCE="$(od -An -N16 -tx8 /dev/urandom | tr -d ' \n')" || fail "nonce generation failed"
MARKER="LINTENV-DRIVER-COMPLETE-$NONCE"
DOCMARKER="DOCSCAN-COMPLETE-$NONCE"

# The default environment-linter set minus docBlame (see the header comment), sorted.
# The docstring-scan driver verifies this against the environment and fails if the
# default set drifts, so a stale list here cannot silently narrow the lint.
LINTERS="checkType defsWithUnderscore deprecatedNoSince impossibleInstance nonClassInstance simpComm simpNF structureInType subsetDotNotationLinter synTaut tacticDocs unusedArguments unusedHavesSuffices"

# $LINTERS rendered as Lean string literals, for the freshness guard in the driver.
LINTERS_LEAN=$(printf '"%s", ' $LINTERS | sed 's/, $//')

MODULE_IMPORT_LIST="$TMP/modules.txt"
find TauCeti -name '*.lean' | LC_ALL=C sort | sed 's/\.lean$//; s|/|.|g' > "$MODULE_IMPORT_LIST"
mods=$(wc -l < "$MODULE_IMPORT_LIST")
[ "${mods:-0}" -gt 0 ] || fail "found no TauCeti/*.lean modules — the lint is miswired"

# --- 1. docstring scan (fast; see the docBlame exclusion rationale above) ----------
# A LEGACY (non-module) driver with plain imports: the non-module root imports the
# closure at the `private` olean level, where docstrings and true declaration kinds
# are visible (they are NOT in a module-style driver; see the header comment).
{
  sed 's/^/import /' "$MODULE_IMPORT_LIST"
  cat <<EOF

open Lean Meta in
/-- docBlame-parity kind: \`some kindWord\` iff the declaration requires a docstring. -/
def docscanKind? (declName : Name) : MetaM (Option String) := do
  if (← getEnv).isAutoDecl declName then return none
  if ← isInstance declName then return none
  if let .str p _ := declName then
    if ← isInstance p then return none
  if let .str _ s := declName then
    if s == "parenthesizer" || s == "formatter" || s == "delaborator" || s == "quot" then
      return none
  match ← getConstInfo declName with
  | .axiomInfo .. => return some "axiom"
  | .opaqueInfo .. => return some "constant"
  | .defnInfo info =>
    if (← isProjectionFn declName) && (← isProp info.type) then return none
    return some "definition"
  | .inductInfo .. => return some "inductive"
  | _ => return none

open Lean in
run_meta do
  let env ← getEnv
  -- Freshness guard (see the header comment): the explicit \`#lint only\` list in
  -- scripts/lint-env.sh must still equal the default linter set minus docBlame.
  let expected : Array String := #[$LINTERS_LEAN]
  let mut actual : Array String := #[]
  for (name, _, dflt) in Batteries.Tactic.Lint.batteriesLinterExt.getState env do
    if dflt && name != \`docBlame then actual := actual.push s!"{name}"
  actual := actual.qsort (· < ·)
  unless actual == expected do
    throwError "the default env-linter set changed: scripts/lint-env.sh runs {expected} \
      but the environment's defaults minus docBlame are {actual}; update LINTERS in \
      scripts/lint-env.sh (and triage any new linter's findings)"
  let modNames := env.allImportedModuleNames
  let candidates : Array Name := env.constants.fold (init := #[]) fun acc declName _ =>
    match env.getModuleIdxFor? declName with
    | some idx =>
      match modNames[idx.toNat]? with
      | some m => if m == \`TauCeti || (\`TauCeti).isPrefixOf m then acc.push declName else acc
      | none => acc
    | none => acc
  let mut scanned := 0
  let mut documented := 0
  let mut undoc := 0
  for declName in candidates do
    if let some kind ← docscanKind? declName then
      scanned := scanned + 1
      if (← findDocString? env declName).isSome then
        documented := documented + 1
        IO.println s!"DOCSCAN-ALL {declName} documented"
      else
        undoc := undoc + 1
        IO.println s!"DOCSCAN-ALL {declName} undocumented"
        IO.println s!"DOCSCAN {declName} /- {kind} missing documentation string -/"
  -- \`@[nolint ...]\` enumeration (see the header comment): a parametric attribute can
  -- only be applied in the module that declares its target, so enumerating the
  -- persistent nolint entries of every TauCeti module is exhaustive for anything that
  -- could silence the \`#lint\` driver. The default (exported) olean level is read —
  -- the level \`ParametricAttribute.getParam?\`, and hence the linter framework's
  -- \`shouldBeLinted\`, consults. (Do NOT read \`level := .server\` here: forcing the
  -- server-level extension state deadlocks under a legacy import.) Imported-entry
  -- visibility is calibrated below against Batteries/Mathlib, which are known to
  -- carry nolint entries of their own.
  let mut nolints := 0
  let mut importedNolintEntries := 0
  for idx in [0:modNames.size] do
    let midx : ModuleIdx := idx
    let entries := Batteries.Tactic.Lint.nolintAttr.ext.getModuleEntries env midx
    importedNolintEntries := importedNolintEntries + entries.size
    if let some m := modNames[idx]? then
      if m == \`TauCeti || (\`TauCeti).isPrefixOf m then
        for (decl, linterNames) in entries do
          for l in linterNames do
            IO.println s!"NOLINT {l} {decl}"
            nolints := nolints + 1
  if importedNolintEntries == 0 then
    throwError "the @[nolint] enumeration is blind: no persistent nolint entries are \
      visible in ANY imported module, yet Batteries/Mathlib are known to carry some — \
      the attribute-extension API moved; fix the enumeration in scripts/lint-env.sh, \
      do not allowlist around this"
  IO.println s!"DOCSCAN-SUMMARY scanned={scanned} documented={documented} undocumented={undoc} nolints={nolints} $DOCMARKER"
EOF
} > "$DOCDRIVER"

if ! lake env lean "$DOCDRIVER" > "$TMP/docscan.txt" 2>&1; then
  cat "$TMP/docscan.txt"
  fail "driver failure: the docstring-scan driver did not elaborate cleanly — see output above"
fi
nsummaries=$(grep -c "^DOCSCAN-SUMMARY scanned=[0-9]* documented=[0-9]* undocumented=[0-9]* nolints=[0-9]* $DOCMARKER\$" "$TMP/docscan.txt" || true)
if [ "${nsummaries:-0}" -ne 1 ]; then
  cat "$TMP/docscan.txt"
  fail "driver failure: expected exactly 1 docstring-scan summary line, found ${nsummaries:-0}"
fi
summary=$(grep "^DOCSCAN-SUMMARY .* $DOCMARKER\$" "$TMP/docscan.txt")
# NB space-anchored keys: a bare `documented=` would greedily match inside `undocumented=`.
scanned=$(echo "$summary" | sed -n 's/.* scanned=\([0-9]*\).*/\1/p')
documented=$(echo "$summary" | sed -n 's/.* documented=\([0-9]*\).*/\1/p')
undocumented=$(echo "$summary" | sed -n 's/.* undocumented=\([0-9]*\).*/\1/p')
nolints=$(echo "$summary" | sed -n 's/.* nolints=\([0-9]*\).*/\1/p')
ndocviol=$(grep -c '^DOCSCAN ' "$TMP/docscan.txt" || true)
[ "${ndocviol:-0}" -eq "$undocumented" ] \
  || { cat "$TMP/docscan.txt"; fail "driver failure: docstring-scan summary claims $undocumented violation(s) but ${ndocviol:-0} DOCSCAN line(s) parsed"; }
# Every scanned declaration is echoed as a `DOCSCAN-ALL <decl> <status>` line; the
# line count and per-status tallies must match the nonce-protected summary, so forged
# DOCSCAN-ALL lines (which could otherwise fake the sentinel/coverage checks below)
# break these counts.
nall=$(grep -c '^DOCSCAN-ALL ' "$TMP/docscan.txt" || true)
[ "${nall:-0}" -eq "$scanned" ] \
  || { cat "$TMP/docscan.txt"; fail "driver failure: docstring-scan summary claims $scanned scanned but ${nall:-0} DOCSCAN-ALL line(s) parsed"; }
nall_doc=$(awk '$1 == "DOCSCAN-ALL" && $3 == "documented"' "$TMP/docscan.txt" | wc -l)
nall_undoc=$(awk '$1 == "DOCSCAN-ALL" && $3 == "undocumented"' "$TMP/docscan.txt" | wc -l)
[ "$nall_doc" -eq "$documented" ] && [ "$nall_undoc" -eq "$undocumented" ] \
  || { cat "$TMP/docscan.txt"; fail "driver failure: DOCSCAN-ALL status tallies ($nall_doc documented, $nall_undoc undocumented) disagree with the summary ($documented, $undocumented)"; }
[ "$scanned" -eq $((documented + undocumented)) ] \
  || fail "docstring scan summary is inconsistent: scanned=$scanned != documented=$documented + undocumented=$undocumented"
[ "$scanned" -gt 0 ] || fail "docstring scan scanned 0 declarations — the scan is miswired"
[ "$documented" -gt 0 ] \
  || fail "docstring scan saw NO docstrings at all ($scanned scanned): docstring visibility is broken (olean docstring storage moved?) — fix the scan, do not baseline this"
# Scanned-count floor: partial blindness (a narrowed candidate set) must not pass
# silently. 500 is ~75% of the 676 declarations scanned when this guard was written
# (2026-07); RAISE it as the library grows, and if it ever fires, fix the scan's
# coverage — do not lower the floor to match a shrunken scan.
[ "$scanned" -ge 500 ] \
  || fail "docstring scan scanned only $scanned declaration(s) (floor: 500): the scan's coverage collapsed — fix the scan, do not baseline this"
# Sentinels: known-documented declarations spread across the library must be scanned
# AND seen as documented; each failure mode is distinct (see the header comment).
for sentinel in TauCeti.GridDiagram.OSet TauCeti.Isotopy TauCeti.AlgebraicGeometry.WeilDivisor.coeff; do
  sentinel_status=$(awk -v d="$sentinel" '$1 == "DOCSCAN-ALL" && $2 == d { print $3 }' "$TMP/docscan.txt")
  case "$sentinel_status" in
    documented) : ;;
    undocumented) fail "docstring visibility is (partially) broken: known-documented sentinel $sentinel scanned as undocumented — fix the scan, do not baseline this" ;;
    "") fail "docstring-scan coverage loss: known-documented sentinel $sentinel was not scanned at all — fix the scan, do not baseline this" ;;
    *) fail "driver failure: sentinel $sentinel has conflicting DOCSCAN-ALL lines" ;;
  esac
done
# Baseline docString entries must still be VISIBLE to the scan: an entry that stops
# violating is ratchetable (fine, handled below), but an entry that vanishes from the
# scanned set entirely means the scan lost coverage, not that the gap was fixed.
if [ "$UPDATE" != 1 ]; then
  for d in $(sed -n 's/^docString //p' "$BASELINE"); do
    awk -v d="$d" '$1 == "DOCSCAN-ALL" && $2 == d { found = 1 } END { exit !found }' "$TMP/docscan.txt" \
      || fail "docstring-scan coverage loss: baseline entry 'docString $d' is no longer scanned at all (not merely fixed) — fix the scan, do not ratchet this entry away"
  done
fi
LC_ALL=C sed -n 's/^DOCSCAN \([^ ]*\).*/docString \1/p' "$TMP/docscan.txt" > "$TMP/violations-docscan.txt"
echo "lint-env: docstring scan: $scanned scanned, $documented documented, $undocumented undocumented."

# --- 1b. `@[nolint <linter>]` ratchet, declaration-level (see step 0) --------------
nnolint=$(grep -c '^NOLINT ' "$TMP/docscan.txt" || true)
[ "${nnolint:-0}" -eq "${nolints:-0}" ] \
  || { cat "$TMP/docscan.txt"; fail "driver failure: docstring-scan summary claims $nolints nolint entr(y/ies) but ${nnolint:-0} NOLINT line(s) parsed"; }
LC_ALL=C sed -n 's/^NOLINT //p' "$TMP/docscan.txt" | LC_ALL=C sort -u > "$TMP/nolints.txt"
LC_ALL=C comm -23 "$TMP/nolints.txt" "$ALLOWLIST" > "$TMP/nolints-new.txt"
if [ -s "$TMP/nolints-new.txt" ]; then
  echo "lint-env: @[nolint <linter>] application(s) under TauCeti/ not accounted for in $ALLOWLIST (as '<linter> <declaration>'):"
  sed 's/^/  /' "$TMP/nolints-new.txt"
  echo "Silencing an environment linter bypasses the baseline. If a @[nolint <linter>] is"
  echo "truly warranted, add the '<linter> <declName>' line to $ALLOWLIST (LC_ALL=C sorted)"
  echo "in the same PR — that file, like this script, must only change via human-reviewed"
  echo "PRs (never via an auto-merged one)."
  fail "unaccounted '@[nolint]' application(s); see the list above"
fi
LC_ALL=C comm -13 "$TMP/nolints.txt" "$ALLOWLIST" > "$TMP/nolints-fixed.txt"
if [ -s "$TMP/nolints-fixed.txt" ]; then
  echo "lint-env: RATCHET — allowlist entr(y/ies) in $ALLOWLIST no longer correspond to a"
  echo "@[nolint] application; please delete these lines (a follow-up PR is fine):"
  sed 's/^/  /' "$TMP/nolints-fixed.txt"
fi

# --- 2. generate the #lint driver: import every TauCeti module, default linters ---
# `set_option linter.hashCommand false` because the driver is generated, not committed;
# the style linter would otherwise flag the bare `#lint`/`#eval`. The trailing `#eval`
# prints a per-run nonce proving the process survived past `#lint` (see SECURITY MODEL).
{
  echo "module"
  sed 's/^/public import /' "$MODULE_IMPORT_LIST"
  echo
  echo "set_option linter.hashCommand false in"
  echo "#lint only $LINTERS in TauCeti"
  echo
  echo "set_option linter.hashCommand false in"
  echo "#eval IO.println \"$MARKER\""
} > "$DRIVER"

# --- 3. elaborate it (exit 1 from lean is EXPECTED when the linters report) -------
if lake env lean "$DRIVER" > "$TMP/out.txt" 2>&1; then
  status=0
else
  status=$?
fi

# --- 4. locate the linter report and parse it fail-closed -------------------------
# Two genuine header shapes (see SECURITY MODEL): N > 0 comes as an error diagnostic
# prefixed with our driver's path; N = 0 comes as a bare info line. Collect both.
awk -v pfx="$DRIVER:" '
  BEGIN { hdr = "-- Found [0-9]+ errors? in [0-9]+ declarations \\(plus [0-9]+ automatically generated ones\\) in TauCeti with [0-9]+ linters$" }
  {
    if (index($0, pfx) == 1) {
      rest = substr($0, length(pfx) + 1)
      if (rest ~ ("^[0-9]+:[0-9]+: error: " hdr)) { print NR " error " rest; next }
    }
    if ($0 ~ ("^" hdr)) print NR " bare " $0
  }' "$TMP/out.txt" > "$TMP/headers.txt"

nheaders=$(wc -l < "$TMP/headers.txt")
if [ "$nheaders" -ne 1 ]; then
  cat "$TMP/out.txt"
  if [ "$nheaders" -eq 0 ]; then
    fail "driver/linter failure: no lint report header found (lean exit $status) — see output above"
  fi
  fail "driver/linter failure: $nheaders report headers found (possible forged report) — see output above"
fi

hdr_lineno=$(awk '{print $1}' "$TMP/headers.txt")
hdr_kind=$(awk '{print $2}' "$TMP/headers.txt")
hdr_count=$(sed -n 's/^.*-- Found \([0-9]*\) errors\{0,1\} in .*/\1/p' "$TMP/headers.txt")
hdr_nlinters=$(sed -n 's/^.* in TauCeti with \([0-9]*\) linters$/\1/p' "$TMP/headers.txt")
[ -n "$hdr_kind" ] && [ -n "$hdr_count" ] && [ -n "$hdr_nlinters" ] \
  || fail "internal error: could not re-parse the report header"

# The header's "with K linters" must match the list we asked `#lint only` to run: a
# report produced by a different linter set (however it arose) is not our report.
nlinters=$(echo "$LINTERS" | wc -w)
if [ "$hdr_nlinters" -ne "$nlinters" ]; then
  cat "$TMP/out.txt"
  fail "driver/linter failure: report header claims $hdr_nlinters linter(s) but $nlinters were requested"
fi

# The report region: everything after the header. The completion marker must appear
# there — it is only printed once elaboration gets PAST the `#lint` command.
tail -n +"$((hdr_lineno + 1))" "$TMP/out.txt" > "$TMP/report.txt"
if ! grep -qF "$MARKER" "$TMP/report.txt"; then
  cat "$TMP/out.txt"
  fail "driver/linter failure: driver did not run to completion (missing nonce marker) — see output above"
fi

# Exit code, header kind, and count must agree: violations mean an anchored error
# header AND a nonzero exit; a clean lint means a bare header with N = 0 AND exit 0.
case "$hdr_kind:$status" in
  error:0) cat "$TMP/out.txt"; fail "driver/linter failure: lint reported errors but lean exited 0" ;;
  bare:0)  if [ "$hdr_count" -ne 0 ]; then
             cat "$TMP/out.txt"
             fail "driver/linter failure: unprefixed report claims $hdr_count violation(s)"
           fi ;;
  error:*) [ "$hdr_count" -gt 0 ] || { cat "$TMP/out.txt"; fail "driver/linter failure: error report with count 0"; } ;;
  bare:*)  cat "$TMP/out.txt"
           fail "driver/linter failure: lean exited $status but the lint itself reported no violations — some other error occurred; see output above" ;;
esac

# One `#check <decl> /- <reason> -/` block per violation (with or without a leading
# `@`, depending on the declaration's binders), grouped into per-linter sections that
# open with a "/- The `<linter>` linter reports:" line — parsed ONLY from the report
# region, by a block-aware state machine. A `#check` block starts at `^#check ` and
# runs to the first line ending in `-/` (possibly the same line); everything inside a
# block is comment CONTENT, never structure, so a violation message that happens to
# contain a section-opener-shaped or `#check`-shaped line (linter messages embed
# attacker-chosen declaration names and types) cannot open a section or a block.
# Section openers are accepted only OUTSIDE blocks, must name a linter from the
# expected `$LINTERS` set (docBlame does not run — see the header comment — so a
# docBlame opener, like any other unexpected name, is structural forgery), and each
# section may open at most once, so real violations cannot be re-attributed to a
# section opened by forged content (a declaration may legitimately sit under TWO
# linters in the baseline, so re-attribution could otherwise dodge it). Every block
# must close before the next one opens, must fall inside a section, and the block
# count must equal N from the header. Any violation of this grammar is a distinct
# driver failure, never a pass.
set +e
LC_ALL=C awk -v expected="$LINTERS" '
  BEGIN {
    n = split(expected, a, " ")
    for (i = 1; i <= n; i++) ok[a[i]] = 1
  }
  inblock {
    if ($0 ~ /^#check /) { code = 4; exit code }  # block did not close before the next #check
    if ($0 ~ /-\/[[:space:]]*$/) inblock = 0      # closing -/ ends the block
    next                                          # inside a block, everything is content
  }
  /^\/- The `.*` linter reports:/ {
    l = $0; sub(/^\/- The `/, "", l); sub(/` linter reports:.*$/, "", l)
    if (!(l in ok)) { code = 5; exit code }       # section name outside the expected set
    if (l in seen)  { code = 6; exit code }       # duplicate section opening
    seen[l] = 1; linter = l
    next
  }
  /^#check / {
    if (linter == "") { code = 3; exit code }     # a violation before any section opener
    name = $2; sub(/^@/, "", name)
    print linter " " name
    if ($0 !~ /-\/[[:space:]]*$/) inblock = 1
    next
  }
  END {
    if (code) exit code
    if (inblock) exit 7                           # unterminated #check block at end of report
  }
' "$TMP/report.txt" > "$TMP/violations-lint.txt"
parse_rc=$?
set -e
if [ "$parse_rc" -ne 0 ]; then
  cat "$TMP/out.txt"
  case "$parse_rc" in
    3) fail "driver/linter failure: a #check block appeared before any linter section" ;;
    4) fail "driver/linter failure: a #check block opened before the previous one closed" ;;
    5) fail "driver/linter failure: a report section names a linter outside the expected set (possible forged section opener)" ;;
    6) fail "driver/linter failure: a linter section was opened twice (possible forged section opener)" ;;
    7) fail "driver/linter failure: unterminated #check block at the end of the report" ;;
    *) fail "driver/linter failure: report parsing failed (awk exit $parse_rc)" ;;
  esac
fi
nchecks=$(wc -l < "$TMP/violations-lint.txt")
if [ "${nchecks:-0}" -ne "$hdr_count" ]; then
  cat "$TMP/out.txt"
  fail "driver/linter failure: header claims $hdr_count violation(s) but $nchecks #check block(s) parsed"
fi

# --- 5. combine, then --update or compare against the grandfathered baseline ------
LC_ALL=C sort -u "$TMP/violations-lint.txt" "$TMP/violations-docscan.txt" > "$TMP/violations.txt"
total=$(wc -l < "$TMP/violations.txt")
echo "lint-env: linted $mods modules; $total (linter, declaration) violation(s)."

if [ "$UPDATE" = 1 ]; then
  cp "$TMP/violations.txt" "$BASELINE"
  echo "lint-env: wrote $total grandfathered entr(y/ies) to $BASELINE."
  exit 0
fi

# Baseline entries that no longer violate: a ratchet reminder, never a failure.
LC_ALL=C comm -13 "$TMP/violations.txt" "$BASELINE" > "$TMP/fixed.txt"
if [ -s "$TMP/fixed.txt" ]; then
  echo
  echo "lint-env: RATCHET — $(wc -l < "$TMP/fixed.txt") baseline entr(y/ies) no longer violate."
  echo "Please delete these lines from $BASELINE (a follow-up PR is fine):"
  sed 's/^/  /' "$TMP/fixed.txt"
fi

# Violations not in the baseline: new debt — fail, and show each check's reasoning.
LC_ALL=C comm -23 "$TMP/violations.txt" "$BASELINE" > "$TMP/new.txt"
if [ -s "$TMP/new.txt" ]; then
  echo
  echo "lint-env: NEW violation(s) not in the grandfathered baseline (as '<linter> <declaration>'):"
  awk 'NR==FNR { want[$0]=1; next }
       /^\/- The `[A-Za-z0-9_]+` linter reports:/ {
         l = $0; sub(/^\/- The `/, "", l); sub(/` linter reports:.*$/, "", l)
         pending = "  [" l "]"
       }
       /^#check / {
         name = $2; sub(/^@/, "", name)
         p = ((l " " name) in want)
         if (p && pending != "") { print pending; pending = "" }
       }
       p { print "  " $0 }
       p && /-\/[[:space:]]*$/ { p = 0; print "" }' "$TMP/new.txt" "$TMP/report.txt"
  awk 'NR==FNR { want[$0]=1; next }
       /^DOCSCAN / {
         name = $2
         if (("docString " name) in want) {
           if (!h) { print "  [docString]"; h = 1 }
           sub(/^DOCSCAN /, "#check ")
           print "  " $0
         }
       }' "$TMP/new.txt" "$TMP/docscan.txt"
  echo
  echo "Fix the declaration per the explanation above (for docString: add a docstring), or"
  echo "— as a deliberate, commented exception — use @[nolint <linter>] plus a"
  echo "'<linter> <declName>' line in $ALLOWLIST (for docString: a baseline entry"
  echo "instead, since the scan ignores @[nolint])."
  echo "If a flagged declaration is NOT in your diff, your branch likely carries a stale"
  echo "copy of a file that main has since cleaned up (the CI build overlays your whole"
  echo "TauCeti/ tree onto current main): merge main into your branch and re-push."
  fail "$(wc -l < "$TMP/new.txt") new violation(s); see the list above"
fi

echo "LINT-ENV: PASS — no new violations ($total grandfathered, $(wc -l < "$TMP/fixed.txt") ratchetable)."
