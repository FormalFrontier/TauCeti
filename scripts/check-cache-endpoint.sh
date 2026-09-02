#!/usr/bin/env bash
# check-cache-endpoint.sh — fail the build unless the configured Mathlib cache read
# endpoint is one this repository has reviewed.
#
# `MATHLIB_CACHE_BASE_URL` comes from a repository variable, which anyone with write
# access can edit, and it decides which host serves the oleans this project's CI imports
# and executes. Mathlib's own Cache/SECURITY.md places a substituted read endpoint outside
# its threat model: the named host chooses the bytes, and the cache validates keys rather
# than bytes. Constraining the variable to `scripts/cache-endpoint-allowlist.txt` puts that
# choice back under the human review AGENTS.md requires for everything else in `scripts/`.
#
# Unset or empty is allowed and means "use the cache tool's own default endpoints" -- the
# tool treats empty as unset, so this is the no-configuration state, not a bypass.
#
# Run with no arguments; reads MATHLIB_CACHE_BASE_URL from the environment.
set -euo pipefail

ALLOWLIST="$(dirname "$0")/cache-endpoint-allowlist.txt"

# Normalise exactly as the cache tool does before it uses the value, so this checks the
# string the tool will actually read rather than the raw one. Mathlib's `normalizeBaseURL`
# is `v.trimAscii.dropEndWhile '/'`, then treats the empty result as unset.
VALUE="${MATHLIB_CACHE_BASE_URL:-}"
VALUE="$(printf '%s' "$VALUE" | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' -e 's:/*$::')"

# The allowlist governs MATHLIB_CACHE_BASE_URL, but that is only the LAST of the cache
# tool's read-endpoint inputs. Its precedence is MATHLIB_CACHE_GET_URL, then --cache-from,
# then MATHLIB_CACHE_FROM, then the container chain that BASE_URL rebases. A higher one set
# anywhere in this job would decide the endpoint without ever consulting the allowlist, so
# refuse rather than check a value that is not the one in force. No workflow here sets them;
# this keeps that true if one ever starts.
for higher in MATHLIB_CACHE_GET_URL MATHLIB_CACHE_FROM; do
  if [ -n "$(eval "printf '%s' \"\${$higher:-}\"")" ]; then
    echo "::error title=A higher-precedence cache endpoint is set::$higher is set, and it outranks MATHLIB_CACHE_BASE_URL in the cache tool's read-endpoint precedence, so the allowlist would not govern where this build fetches from. Unset it, or route the endpoint through MATHLIB_CACHE_BASE_URL and scripts/cache-endpoint-allowlist.txt."
    exit 1
  fi
done

if [ -z "$VALUE" ]; then
  echo "MATHLIB_CACHE_BASE_URL is unset; reads use the cache tool's default endpoints"
  exit 0
fi

if [ ! -f "$ALLOWLIST" ]; then
  echo "::error::$ALLOWLIST is missing, so the configured cache endpoint cannot be checked"
  exit 1
fi

# Compare against the file's non-comment, non-blank lines. Exact match only: a prefix rule
# would accept `https://cache.mathlib.org.example.invalid`, and a suffix rule would accept
# an arbitrary host with a matching tail.
while IFS= read -r line; do
  line="${line%%#*}"
  line="$(printf '%s' "$line" | tr -d '[:space:]')"
  [ -n "$line" ] || continue
  if [ "$VALUE" = "$line" ]; then
    echo "MATHLIB_CACHE_BASE_URL=$VALUE is allowlisted; reads go to that host"
    exit 0
  fi
done < "$ALLOWLIST"

echo "::error title=Mathlib cache endpoint is not allowlisted::MATHLIB_CACHE_BASE_URL is set to '$VALUE', which is not listed in scripts/cache-endpoint-allowlist.txt. That variable decides which host serves the oleans this build imports and executes, so a new endpoint has to be added to the allowlist in a reviewed pull request first."
exit 1
