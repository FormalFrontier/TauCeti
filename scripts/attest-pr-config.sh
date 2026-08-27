#!/usr/bin/env bash
# Attest an exact PR checkout before any command executes its Lake configuration.
#
# Usage:
#   attest-pr-config.sh <merge-base-dir> <candidate-dir> <head-sha> \
#     <event-name> <merge-base-exact:0|1> <pins-changed:0|1>
#
# The lakefile must be inherited byte-for-byte from the merge base. The two pins must be
# ordinary files, and their observed local delta must agree with the immutable GitHub tree check
# performed by pr-build.yml. A changed pin is authorized only after this script returns; the
# separate workflow-pinned check-bump.sh then validates it as a forward move before Lake runs.
set -euo pipefail

MERGE_BASE="${1:?merge-base directory is required}"
CANDIDATE="${2:?candidate directory is required}"
EXPECTED_SHA="${3:?expected head SHA is required}"
EVENT_NAME="${4:?event name is required}"
MERGEBASE_EXACT="${5:-0}"
PINS_CHANGED="${6:-0}"

fail() {
  echo "::error::config-attestation: $*" >&2
  exit 1
}

case "$EXPECTED_SHA" in
  ''|*[!0-9a-f]*) fail "expected head is not a lowercase hexadecimal object ID" ;;
esac
[ "${#EXPECTED_SHA}" = 40 ] || fail "expected head is not a 40-character object ID"
[ "$EVENT_NAME" = "merge_group" ] || [ "$MERGEBASE_EXACT" = "1" ] \
  || fail "the PR merge base was not resolved exactly"
case "$PINS_CHANGED" in
  0|1) ;;
  *) fail "pins-changed must be 0 or 1" ;;
esac

GOT="$(git -C "$CANDIDATE" rev-parse HEAD 2>/dev/null)" \
  || fail "candidate is not a readable Git checkout"
[ "$GOT" = "$EXPECTED_SHA" ] \
  || fail "candidate resolved to $GOT instead of immutable event head $EXPECTED_SHA"

ordinary_file() {
  [ -f "$1" ] && [ ! -L "$1" ]
}

# Lake accepts either spelling. Preserve both presence and bytes from the trusted ancestor so a
# candidate cannot switch which configuration Lake loads.
for FILE in lakefile.toml lakefile.lean; do
  MB="$MERGE_BASE/$FILE"
  HEAD="$CANDIDATE/$FILE"
  if [ -e "$MB" ] || [ -L "$MB" ]; then
    ordinary_file "$MB" || fail "$FILE is not an ordinary file at the merge base"
    ordinary_file "$HEAD" || fail "$FILE is missing or not an ordinary file at the candidate head"
    cmp -s "$MB" "$HEAD" || fail "$FILE differs from the PR merge base"
  elif [ -e "$HEAD" ] || [ -L "$HEAD" ]; then
    fail "$FILE was introduced by the candidate"
  fi
done
ordinary_file "$CANDIDATE/lakefile.toml" \
  || fail "this repository requires an ordinary lakefile.toml"

LOCAL_PIN_DELTA=0
for FILE in lake-manifest.json lean-toolchain; do
  ordinary_file "$MERGE_BASE/$FILE" || fail "$FILE is not an ordinary merge-base pin"
  ordinary_file "$CANDIDATE/$FILE" || fail "$FILE is not an ordinary candidate pin"
  cmp -s "$MERGE_BASE/$FILE" "$CANDIDATE/$FILE" || LOCAL_PIN_DELTA=1
done
[ "$LOCAL_PIN_DELTA" = "$PINS_CHANGED" ] \
  || fail "the local pin delta disagrees with the immutable GitHub tree check"

echo "config-attestation: exact candidate config is safe to validate/build"
