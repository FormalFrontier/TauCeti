#!/usr/bin/env bash
# lake-cache-get.sh — restore TauCeti's OWN root-package oleans from the public Lake
# artifact cache, factored out of .github/workflows/pr-build.yml so ci.yml can use the
# same logic. Both callers want identical semantics: a clean whole cache, or none at all.
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
# A PARTIAL fetch is a different matter. `lake cache get` continues past a failed download and
# exits nonzero (see `lake cache help get`), leaving input-to-output mappings whose artifacts
# never arrived. pr-build's sandboxed build is offline with no cache service configured, so it
# cannot fetch them: Lake logs a warning per affected module and correctly rebuilds it from
# source, but `lake build --iofail` is `--fail-level=info`, so those warnings fail a build in
# which every module compiled. Partial fetches are routine: they cost about a third of
# merge-group builds their cache. Fixed by https://github.com/leanprover/lean4/pull/14651,
# landing in v4.34.0-rc1; see https://github.com/TauCetiProject/TauCeti/issues/2062.
#
# Hence: retry from an EMPTY cache each time, then fall back to no cache at all. Retrying over
# the dirty cache a failed attempt left behind does not work: Lake skips any artifact already
# on disk, so the retry re-fetches only what is still MISSING and never revisits what the failed
# attempt got wrong. It then reports clean and the corruption survives into the build.
# Discarding between attempts is what makes a clean verdict mean the cache is whole; it is
# affordable because a failing attempt aborts in seconds and a full refetch is ~30s.
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

# `lake cache get` cannot be judged by exit status alone. Lake accumulates transfer failures
# into a local `didError` but then tests the stale `s.didError` (Lake/Config/Cache.lean,
# `if s.didError then failure`), so it can log "failed to download some artifacts" and still
# exit 0. An attempt therefore counts as clean only if it exits 0 AND logs no failure
# diagnostic.
# SIMPLIFY ON THE BUMP TO v4.34.0: that stale read is fixed by
# https://github.com/leanprover/lean4/pull/14651 ("fix: lake: gracefully handle curl and IO
# errors during transfer"), which missed v4.33.0-rc2 by hours and was not backported. From
# v4.34.0-rc1 on, drop FAIL_RE and trust `rc` alone. The purge below outlives that bump: it is
# for https://github.com/leanprover/lean4/issues/14670, still open.
#
# `downloaded artifact hash mismatch` must be here. Lake handles a mismatch by deleting the
# artifact and setting `didError`, but the stale `didError` read means the process can still
# exit 0, and the deletion leaves an input-to-output mapping whose artifact is gone. An offline
# build cannot refetch it, so that entry becomes a build failure rather than a rebuild. Treat it
# as unclean so the cache is refetched or dropped.
FAIL_RE='failed to download|output lookup failed|curl exited with code|downloaded artifact hash mismatch'
# A revision with no cached build at all is deterministic: retrying cannot change it, and there
# is nothing partial to discard.
MISS_RE='no outputs found'
# Six attempts, not three. Losing every attempt discards the whole cache and forces a ~22 minute
# full rebuild, which was happening on 4 of 18 sampled builds (the other 14 took 2-3 minutes).
# The cause is lean4#14698: one unreadable artifact throws out of `computeFileHash`, which has
# no try/catch, so a single ENOENT aborts the entire fetch and discards every artifact already
# downloaded. Which artifact trips it varies between attempts, so re-fetching genuinely tends to
# succeed; at the observed per-attempt failure rate six attempts take whole-cache loss from
# roughly 22% to roughly 5%. Reduce this again once the fix (lean4#14651) reaches a released
# toolchain: it is on master only, and v4.33.0-rc2 was branched before it landed.
ATTEMPTS=6
clean=0
for attempt in $(seq 1 $ATTEMPTS); do
  LOG="${RUNNER_TEMP:-/tmp}/cache-get-$attempt.log"
  rc=0
  ( cd "$PROJECT_DIR" && LAKE_CONFIG="$CFG" lake cache get --service tauceti-public \
      --repo TauCetiProject/TauCeti ) > "$LOG" 2>&1 || rc=$?
  cat "$LOG"
  if [ "$rc" = 0 ] && ! grep -qE "$FAIL_RE" "$LOG"; then clean=1; break; fi
  if grep -qE "$MISS_RE" "$LOG"; then break; fi
  # `[ ... ] && sleep` would abort the script under `bash -e` on the last attempt, when the
  # test is false and the whole list returns nonzero. Use a plain `if`.
  if [ "$attempt" != "$ATTEMPTS" ]; then
    echo "::notice::lake cache get attempt $attempt of $ATTEMPTS did not complete cleanly; discarding the partial cache and retrying"
    # Sleep BEFORE discarding. A failed `lake cache get` returns as soon as one transfer errors,
    # while its sibling curl/leantar processes are still writing into the cache dir; discarding
    # at that instant races them. This is not a throttling backoff: the read endpoint serves
    # these artifacts byte-identically under 48-way concurrency, so the failures are the Lake bug
    # above rather than rate limiting, and a short fixed pause is enough to let the stragglers
    # finish.
    sleep 10
    # Must precede the retry: see the header. Without this, attempt N+1 skips every artifact this
    # attempt already wrote, including the broken ones, and a clean exit from it says nothing
    # about the entries that made this attempt fail.
    discard_cache
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
