#!/usr/bin/env bash
# lake-cache-get.sh — restore TauCeti's OWN root-package oleans from the public Lake
# artifact cache, factored out of .github/workflows/pr-build.yml so ci.yml can use the
# same logic. Both callers want identical final semantics: a clean whole cache, or none at all.
#
# Usage: bash scripts/lake-cache-get.sh <project-dir>
#
# Reads PUBLIC_ARTIFACT_ENDPOINT / PUBLIC_REVISION_ENDPOINT from the environment (the
# LAKE_CACHE_*_PUBLIC repo variables). Expects LAKE_CACHE_DIR to be <project-dir>/.lake/cache.
# On an unclean outcome it discards the cache and appends the LAKE_* disable lines to
# $GITHUB_ENV, so the caller's build proceeds exactly as if the cache were switched off.
#
# Anonymous GETs from the PUBLIC read host (a different host than the S3 API endpoint the
# trusted upload uses). Looks up the root-package oleans for the checkout's revision --
# backtracking up to --max-revs ancestors, and unpacks them into $LAKE_CACHE_DIR. This is
# trusted, publisher-built data: no token is in reach and no PR code runs (lakefile.toml is
# declarative and base-trusted). Mathlib's oleans are NOT here; they come from
# `lake exe cache get`.
#
# A TOTAL miss is non-fatal: the build just recompiles from scratch, as when the cache is off.
# A PARTIAL fetch is non-fatal too, but must not reach the offline build. Since v4.34.0-rc1,
# Lake downloads to temporary files, verifies their hashes, atomically installs only valid
# artifacts, and returns failure when any transfer fails. A retry over the same cache therefore
# preserves verified artifacts and fetches only those still missing. If every attempt fails, we
# discard the partial cache before the build so its final behavior remains exactly the same as
# when the cache is switched off. See https://github.com/leanprover/lean4/pull/14651 and
# https://github.com/TauCetiProject/TauCeti/issues/2062.
set -euo pipefail

PROJECT_DIR="${1:?usage: lake-cache-get.sh <project-dir>}"
: "${PUBLIC_ARTIFACT_ENDPOINT:?PUBLIC_ARTIFACT_ENDPOINT is required}"
: "${PUBLIC_REVISION_ENDPOINT:?PUBLIC_REVISION_ENDPOINT is required}"

# Define the public read service in a Lake system config and select it with `--service`
# (the env-var form of endpoint config is deprecated). Anonymous GETs, so no key here.
CFG="${RUNNER_TEMP:-/tmp}/lake-cache.toml"
cat > "$CFG" <<TOML
cache.defaultService = "tauceti-public"
[[cache.service]]
name = "tauceti-public"
kind = "s3"
artifactEndpoint = "$PUBLIC_ARTIFACT_ENDPOINT"
revisionEndpoint = "$PUBLIC_REVISION_ENDPOINT"
TOML

# Discarding the cache must never fail. A plain `rm -rf` on a directory that Lake's stragglers
# are still writing into exits 1 with "Directory not empty", and under `set -e` that killed the
# whole build, which is worse than the partial cache it was clearing. Rename first (atomic,
# and unaffected by concurrent writes under the old path), then delete the renamed copy
# best-effort. What matters for correctness is only that the cache PATH is empty for the next
# attempt, not that the bytes are reclaimed promptly.
discard_cache() {
  local d="$PROJECT_DIR/.lake/cache"
  [ -e "$d" ] || return 0
  if mv "$d" "$d.discard.$$" 2>/dev/null; then
    rm -rf "$d.discard.$$" 2>/dev/null || true
  else
    rm -rf "$d" 2>/dev/null || true
  fi
  return 0
}

# Lake v4.34.0-rc1 and later correctly return failure when any transfer, lookup, or hash check
# fails. Successful artifacts have already been verified and atomically installed, so they are
# safe to retain for the next attempt.
# A revision with no cached build at all is deterministic: retrying cannot change it, and there
# is nothing partial to discard.
MISS_RE='no outputs found'
# Three attempts are enough now that each retry fetches only artifacts still missing rather than
# throwing away and redownloading the whole cache.
ATTEMPTS=3
clean=0
for attempt in $(seq 1 $ATTEMPTS); do
  LOG="${RUNNER_TEMP:-/tmp}/cache-get-$attempt.log"
  rc=0
  ( cd "$PROJECT_DIR" && LAKE_CONFIG="$CFG" lake cache get --service tauceti-public \
      --repo TauCetiProject/TauCeti ) > "$LOG" 2>&1 || rc=$?
  cat "$LOG"
  if [ "$rc" = 0 ]; then clean=1; break; fi
  if grep -qE "$MISS_RE" "$LOG"; then break; fi
  # `[ ... ] && sleep` would abort the script under `bash -e` on the last attempt, when the
  # test is false and the whole list returns nonzero. Use a plain `if`.
  if [ "$attempt" != "$ATTEMPTS" ]; then
    echo "::notice::lake cache get attempt $attempt of $ATTEMPTS did not complete cleanly; retaining verified artifacts and retrying missing ones"
    # Give a transient connection failure a brief backoff. Lake has waited for curl to exit and
    # has removed or left uninstalled any invalid temporary artifacts before returning.
    sleep 2
  fi
done

if [ "$clean" != 1 ]; then
  # Purge on ANY unclean outcome, not just a recognised download failure: an earlier attempt may
  # have written mappings whose artifacts never arrived, and the last attempt's log alone does
  # not witness that. A cache the build cannot fully resolve is worse than none, because each
  # unresolvable entry becomes a build failure rather than a rebuild under `--iofail`.
  # Discarding it restores the no-cache path exactly.
  echo "::warning::lake cache get did not complete cleanly; discarding the cache and building TauCeti/ from scratch"
  discard_cache
  # Empty is NOT off: Lake parses an empty LAKE_ARTIFACT_CACHE as "unspecified" and then defaults
  # artifact-cache reads to true, and an empty LAKE_CACHE_DIR falls back to the workspace's own
  # .lake/cache. Say false explicitly rather than relying on the directory above having just been
  # deleted.
  {
    echo "LAKE_ARTIFACT_CACHE=false"
    echo "LAKE_RESTORE_ARTIFACTS=false"
    echo "LAKE_CACHE_DIR="
  } >> "${GITHUB_ENV:-/dev/null}"
fi
