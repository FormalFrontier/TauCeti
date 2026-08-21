#!/usr/bin/env bash
# Runs INSIDE the landrun sandbox (offline, no token, writes confined to
# base/.lake). For every prepared Lean source under <prep>/src, elaborate it
# with Mathlib's countHeartbeats linter and write the linter's output next to
# it as <name>.hb. The library has already been built by the caller, so a
# file's imports resolve from the built oleans and only these single files are
# re-elaborated (out of tree, like Lean Pool's proof profiler).
#
# Advisory: a file that fails to elaborate records the failure in its own .hb
# log (the caller's render step reports it) and never fails this script, so one
# bad file cannot sink the whole profile.
#
# Usage: measure.sh <prep-dir>   (with the working directory at the built base)
set -uo pipefail
prep="${1:?usage: measure.sh <prep-dir>}"

jobs="$(nproc)"
[ "$jobs" -gt 1 ] && jobs=$((jobs - 1))

# One file per worker: elaborate it and capture stdout+stderr as its .hb log.
# `|| true` keeps a failing elaboration from tripping the run; the .hb log
# still holds whatever the linter and any error printed.
find "$prep/src" -name '*.lean' -print0 \
  | xargs -0 -P "$jobs" -I{} bash -c '
      f="$1"
      out="${f%.lean}.hb"
      # This advisory re-elaboration still executes untrusted Lean code, so it
      # gets the same per-process wall-time limit as the required build.
      lake env "$WATCHDOG_TOOLCHAIN/bin/lean" \
        -Dlinter.countHeartbeats=true "$f" > "$out" 2>&1 || true
    ' _ {}

echo "Measured $(find "$prep/src" -name '*.hb' | wc -l) file(s)."
