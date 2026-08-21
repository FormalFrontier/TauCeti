#!/usr/bin/env bash
# sandbox-build.sh — the offline, landrun-sandboxed build + audits + environment lint of
# the overlaid TauCeti/ sources, factored out of .github/workflows/pr-build.yml.
#
# pr-build.yml invokes this inside landrun with a fixed, comment-free one-liner
# (`cd base && exec bash scripts/sandbox-build.sh`), so the workflow's `bash -c` payload
# can no longer be broken by an apostrophe or a stray quote in a comment: all the prose
# and its punctuation live here, in a file the shell reads as a script rather than as a
# single-quoted `-c` argument. (A comment reading "Mathlib's default" once closed that
# single-quoted argument early and reddened every PR build; see #694.)
#
# This is a TRUSTED base copy. Only the PR's TauCeti/ is overlaid into the sandbox;
# scripts/ is not, and a PR that edits scripts/ is routed to a human by the scope guard —
# so this script cannot be swapped out to escape the sandbox, even though it elaborates
# the PR's (untrusted) TauCeti/ code, which is the whole reason it runs under landrun.
#
# cwd on entry is the trusted `base` checkout, with the PR's TauCeti/ already overlaid.
set -euxo pipefail

export TMPDIR="$PWD/.lake/tmp"

# Lake normally invokes Lean directly. Route every compiler process through a
# trusted wall-clock watchdog instead. This script and the wrapper are the
# trusted base copies; the PR can overlay only TauCeti/, and landrun does not
# pass timeout-control variables, so PR code cannot raise or disable the 300s
# deadline. The wrapper and Lean both remain inside the same landrun sandbox.
test -n "${WATCHDOG_TOOLCHAIN:-}"
test -x "$WATCHDOG_TOOLCHAIN/bin/lean"
export LAKE_OVERRIDE_LEAN=true
export LEAN="$WATCHDOG_TOOLCHAIN/bin/lean"

# Build the overlaid TauCeti/ against the trusted base config. landrun keeps this
# offline and confines writes to base/.lake.
#
# --iofail requires a SILENT build, the way Mathlib does (its CI runs `lake build --iofail`): it is
# `--fail-level=info`, so the build fails if any module logs an `info:` (or warning/error) — a stray
# #check/#eval, a `simp?`/`ring_nf?`-style "Try this: …" suggestion, a linter note. A clean elaboration
# logs nothing above trace, so this is exit-code enforcement, not output scraping.
lake build --iofail

# Axiom audit: inspect the built environment and reject any axiom outside
# {propext, Classical.choice, Quot.sound} — catching sorry, native_decide, and
# home-rolled axioms, including ones reaching in through imports.
lake exe axioms

# Module-system audit: every TauCeti/ module must opt into the Lean module system
# (read from each compiled module's isModule flag, not a textual grep).
lake exe module-system

# Environment lint: Mathlib's default `#lint` set minus docBlame, plus a
# module-system-reliable docstring scan, compared against the grandfathered baseline in
# scripts/lint-baseline.txt. Script, baseline, and the @[nolint <linter>] allowlist
# (scripts/lint-nolints-allowlist.txt) are trusted base copies, and its report parsing
# is fail-closed (see the SECURITY MODEL in the script). Fails on new violations or
# unaccounted nolints; fixed baseline entries print a ratchet reminder only.
bash scripts/lint-env.sh

# Source style lint. The trusted wrapper uses the shared validated TauCeti/ module list, applies
# Mathlib's copyright/Authors checks (excluding the deliberately empty root), and generates the
# text-linter import root under .lake/ without relying on TauCeti.lean's imports.
bash scripts/lint-style.sh
