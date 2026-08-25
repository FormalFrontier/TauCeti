#!/usr/bin/env bash
# Toolchain-shaped Lake wrapper: put one hard deadline around each Lean process.
#
# GNU timeout uses a separate process group by default, sends TERM at the first
# deadline, and escalates to KILL after --kill-after. The production landrun
# environment does not pass the TAUCETI_* variables below; they exist only so
# the trusted unit test can exercise this in milliseconds rather than minutes.
set -uo pipefail

deadline="${TAUCETI_LEAN_TIMEOUT_SECONDS:-300}"
grace="${TAUCETI_LEAN_KILL_GRACE_SECONDS:-30}"
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)
toolchain_root=${script_dir%/bin}

# Lake probes the command named by LEAN, then reconstructs <reported-prefix>/bin/lean.
# Reporting this wrapper's prepared, read-only toolchain root keeps every later
# compiler invocation on the wrapper instead of silently switching back to the
# underlying executable.
if [ "$#" = 1 ] && [ "$1" = --print-prefix ]; then
  printf '%s\n' "$toolchain_root"
  exit 0
fi

lean_command="$script_dir/lean-real"
if [ ! -x "$lean_command" ]; then
  echo "error: trusted Lean watchdog toolchain is missing bin/lean-real" >&2
  exit 127
fi

timeout --signal=TERM --kill-after="$grace" "$deadline" "$lean_command" "$@"
status=$?
if [ "$status" = 124 ] || [ "$status" = 137 ]; then
  source='<unknown module>'
  for argument in "$@"; do
    case "$argument" in *.lean) source="$argument" ;; esac
  done
  echo "error: Lean process for $source exceeded the ${deadline}s wall-clock limit (TERM, then KILL after ${grace}s)" >&2
fi
exit "$status"
