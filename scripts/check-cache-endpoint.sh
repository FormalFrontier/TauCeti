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
# Two other cache variables fail the build outright when set to a non-empty value:
# MATHLIB_CACHE_GET_URL, which the allowlisted base never reaches, and MATHLIB_CACHE_FROM,
# which keeps the base but replaces the container chain. See the refusals below for why.
# An operator who still has the superseded MATHLIB_CACHE_GET_URL variable defined has to
# clear it, or every build fails here.
#
# Run with no arguments; reads MATHLIB_CACHE_BASE_URL from the environment.
set -euo pipefail

ALLOWLIST="$(dirname "$0")/cache-endpoint-allowlist.txt"

# Normalise exactly as the cache tool does before it uses the value, so this checks the
# string the tool will actually read rather than the raw one. Mathlib's `normalizeBaseURL`
# (`Cache/Infra.lean`, which `getBaseURLFrom` and so `Container.getURL` read the value
# through) is `v.trimAscii.dropEndWhile '/'`, then treats the empty result as unset, and its
# `Char.isWhitespace` is exactly space, tab, CR and LF. Trimming any wider set -- which is
# what `[[:space:]]` means in a UTF-8 locale, where it also covers vertical tab, form feed
# and the Unicode spaces -- would accept a value the tool then resolves to a different URL.
shopt -s extglob
WS=$' \t\r\n'
normalize() {
  local v="$1"
  v="${v##+(["$WS"])}"
  v="${v%%+(["$WS"])}"
  v="${v%%+(/)}"
  printf '%s' "$v"
}

VALUE="$(normalize "${MATHLIB_CACHE_BASE_URL:-}")"

# Two other read-endpoint inputs are refused outright. `effectiveGetURLs` in Mathlib's
# `Cache/Requests.lean` resolves the read chain, and its docstring lists the precedence
# "(most specific wins)": MATHLIB_CACHE_GET_URL, the `--cache-from` CLI flag,
# MATHLIB_CACHE_FROM, then the default container chain. The two env vars are refused for
# different reasons, so they get different messages. No workflow here sets either; these
# checks keep that true if one ever starts. (`--cache-from` is a flag on the `cache` command
# line, not something this script can observe; no `lake exe cache get` call here passes it.)
#
# Both are normalised first, because the tool treats a whitespace-only value as unset too;
# refusing one would fail a build the tool would have run unaffected.

# MATHLIB_CACHE_GET_URL returns a single flat URL and never consults the base at all, so it
# decides the host outright and the allowlist never governs the fetch.
if [ -n "$(normalize "${MATHLIB_CACHE_GET_URL-}")" ]; then
  echo "::error title=A cache endpoint that bypasses the allowlist is set::MATHLIB_CACHE_GET_URL is set. It names one flat read endpoint and bypasses MATHLIB_CACHE_BASE_URL entirely, so the allowlist would not govern where this build fetches from. Unset it, and route the endpoint through MATHLIB_CACHE_BASE_URL and scripts/cache-endpoint-allowlist.txt."
  exit 1
fi

# MATHLIB_CACHE_FROM does keep the base: its branch of `effectiveGetURLs` ends in
# `chainWithGetURLs`, whose URLs are `{getBaseURL}/{azureContainerName}`, so the host stays
# the allowlisted one. What it replaces is the container chain, and that chain is
# trust-ordered (see the `Container` docstrings in `Cache/Infra.lean`): it can put a
# container any fork's PR build writes to, such as 'forks', ahead of the master container
# this project builds against. Refusing it keeps the containers a reviewed decision too.
if [ -n "$(normalize "${MATHLIB_CACHE_FROM-}")" ]; then
  echo "::error title=A cache container override is set::MATHLIB_CACHE_FROM is set. Reads would still resolve under the allowlisted base, but it replaces the cache tool's trust-ordered container chain, which can put a less-trusted container such as 'forks' ahead of master. Unset it; which containers this project reads is a reviewed decision, not a repository-variable one."
  exit 1
fi

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
# `|| [ -n "$line" ]` so a final line with no trailing newline is still read: an allowlist
# saved without one would otherwise silently lose its last entry.
while IFS= read -r line || [ -n "$line" ]; do
  line="${line%%#*}"
  # Edge whitespace only. Deleting it everywhere would let `https://cache.math lib.org`
  # through as an entry the tool could never produce.
  line="$(normalize "$line")"
  [ -n "$line" ] || continue
  case "$line" in
    *[$WS]*)
      echo "::error::scripts/cache-endpoint-allowlist.txt has an entry containing whitespace: '$line'"
      exit 1 ;;
  esac
  if [ "$VALUE" = "$line" ]; then
    echo "MATHLIB_CACHE_BASE_URL=$VALUE is allowlisted; reads go to that host"
    exit 0
  fi
done < "$ALLOWLIST"

echo "::error title=Mathlib cache endpoint is not allowlisted::MATHLIB_CACHE_BASE_URL is set to '$VALUE', which is not listed in scripts/cache-endpoint-allowlist.txt. That variable decides which host serves the oleans this build imports and executes, so a new endpoint has to be added to the allowlist in a reviewed pull request first."
exit 1
