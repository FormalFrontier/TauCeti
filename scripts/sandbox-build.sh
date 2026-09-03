#!/usr/bin/env bash
# sandbox-build.sh — the offline, landrun-sandboxed build + audits + environment lint of
# the candidate TauCeti sources, factored out of .github/workflows/pr-build.yml.
#
# pr-build.yml invokes this workflow-pinned copy inside landrun with a fixed, comment-free
# one-liner, so the workflow's `bash -c` payload
# can no longer be broken by an apostrophe or a stray quote in a comment: all the prose
# and its punctuation live here, in a file the shell reads as a script rather than as a
# single-quoted `-c` argument. (A comment reading "Mathlib's default" once closed that
# single-quoted argument early and reddened every PR build; see #694.)
#
# This is a TRUSTED workflow-pinned copy mounted separately from the exact candidate checkout.
# Candidate scripts are never invoked by the required build, even when a human-owned
# infrastructure PR changes them.
#
# cwd on entry is the exact immutable candidate checkout.
set -euxo pipefail

export TMPDIR="$PWD/.lake/tmp"
TRUSTED_SCRIPTS="${TAUCETI_TRUSTED_SCRIPTS:?trusted script directory is required}"
test -d "$TRUSTED_SCRIPTS"

# Lake normally invokes Lean directly. Route every compiler process through a
# trusted wall-clock watchdog instead. This script and the wrapper are the
# workflow-pinned copies, and landrun does not pass timeout-control variables,
# so candidate code cannot raise or disable the 300s
# deadline. The wrapper and Lean both remain inside the same landrun sandbox.
test -n "${WATCHDOG_TOOLCHAIN:-}"
test -x "$WATCHDOG_TOOLCHAIN/bin/lean"
export LAKE_OVERRIDE_LEAN=true
export LEAN="$WATCHDOG_TOOLCHAIN/bin/lean"

# Build the exact candidate against its attested Lake config. landrun keeps this offline and
# confines writes to the candidate's .lake directory.
#
# --iofail requires a SILENT build, the way Mathlib does (its CI runs `lake build --iofail`): it is
# `--fail-level=info`, so the build fails if any module logs an `info:` (or warning/error) — a stray
# #check/#eval, a `simp?`/`ring_nf?`-style "Try this: …" suggestion, a linter note. A clean elaboration
# logs nothing above trace, so this is exit-code enforcement, not output scraping.
lake build --iofail

# Axiom audit: inspect the built environment and reject any axiom outside
# {propext, Classical.choice, Quot.sound} — catching sorry, native_decide, and
# home-rolled axioms, including ones reaching in through imports.
lake env "$WATCHDOG_TOOLCHAIN/bin/lean" --run "$TRUSTED_SCRIPTS/Axioms.lean"

# Module-system audit: every TauCeti/ module must opt into the Lean module system
# (read from each compiled module's isModule flag, not a textual grep).
lake env "$WATCHDOG_TOOLCHAIN/bin/lean" --run "$TRUSTED_SCRIPTS/ModuleSystem.lean"

# Environment lint: Mathlib's default `#lint` set minus docBlame, plus a
# module-system-reliable docstring scan, compared against the grandfathered baseline in
# scripts/lint-baseline.txt. Script, baseline, and the @[nolint <linter>] allowlist
# (scripts/lint-nolints-allowlist.txt) are workflow-pinned trusted copies, and its report parsing
# is fail-closed (see the SECURITY MODEL in the script). Fails on new violations or
# unaccounted nolints; fixed baseline entries print a ratchet reminder only.
bash "$TRUSTED_SCRIPTS/lint-env.sh"

# Source style lint. The trusted wrapper uses the shared validated TauCeti/ module list, applies
# Mathlib's copyright/Authors checks (excluding the deliberately empty root), and generates the
# text-linter import root under .lake/ without relying on TauCeti.lean's imports.
bash "$TRUSTED_SCRIPTS/lint-style.sh"

# A merge-group commit that passes every audit is the exact commit GitHub will land. Pack its
# root-package outputs while still inside landrun, after the final operation that executes
# candidate code. The host uploads only this data-only staging tree to a fresh, secret-isolated
# publisher job. Ordinary PRs and installations without upload endpoints leave this disabled.
if [ "${STAGE_LAKE_CACHE:-}" = "1" ]; then
  if ! grep -Eq '^[[:space:]]*platformIndependent[[:space:]]*=[[:space:]]*true' lakefile.toml; then
    echo "lakefile.toml no longer sets platformIndependent = true" >&2
    exit 1
  fi
  if grep -Eq '^[[:space:]]*(fixedToolchain|bootstrap)[[:space:]]*=[[:space:]]*true' lakefile.toml; then
    echo "lakefile.toml changes the toolchain cache scope" >&2
    exit 1
  fi

  export LAKE_ARTIFACT_CACHE=true
  export LAKE_RESTORE_ARTIFACTS=true
  export LAKE_NO_CACHE=true
  export LAKE_CACHE_DIR="$PWD/.lake/cache"
  lake build >/dev/null
  lake build --no-build -o .lake/outputs.jsonl
  echo "root-package mapping entries: $(wc -l < .lake/outputs.jsonl)"
  rm -rf .lake/cache-staging
  lake cache stage .lake/outputs.jsonl .lake/cache-staging
fi
