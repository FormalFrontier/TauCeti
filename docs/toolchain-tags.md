# Toolchain tags

Tau Ceti carries a plain `vX.Y.Z` tag for each Lean release, the way Mathlib does, so a
downstream project on Lean `v4.33.0` can check out `v4.33.0` here and get a tree that
builds against Mathlib's own `v4.33.0`.

`scripts/toolchain_tags.py --audit` is the authority on what exists, what does not, and
how to repair the difference. It prints the policy with its report, so nothing below is
needed to act on a gap. This file records the reasoning that the report has no room for.

## What a tag means

For every Lean release `X` this repository's history can reach, the tag `vX` points at
the **first** `main`-reachable commit whose `lean-toolchain` is exactly
`leanprover/lean4:X` and whose Mathlib pin is at or after Mathlib's own `vX` tag commit
`M`. The pin is, in order of preference:

1. **exact**, `M` itself. The commit is either already on `main`, or is a single commit on
   a `releases/vX` branch whose parent is a `main` commit and which changes only
   `lake-manifest.json` and `lean-toolchain`.
2. **inexact**, when no exact commit exists or the exact one will not compile: the first
   `main` commit on toolchain `X`. The annotated tag message records how many Mathlib
   commits past `M` the pin is.

A tag is created only after a from-source build of that commit, with the Lake artifact
cache off, passes the audits and lints that commit defines, and its oleans have been
published to the Lake cache and read back. **Tags are never moved.** A tag that disagrees
with the policy is a question for a human, and no tool here will delete or force one.

### Why "first" rather than the richest commit

For the exact rung it is forced. A run of commits sharing a pin at the tip of `main` is
open-ended: `main` keeps appending to it until the next bump. Under "last" the tag would
want to move every day and would never be idempotent. "First" is fixed the moment the run
begins. The inexact rung follows the same rule so that `vX` means one thing, at the cost
of some mathematics: `v4.31.0-rc1` lands on the repository's initial commit, because that
is where `main`'s `v4.31.0-rc1` era starts.

## What the cache guarantee covers, and what it cannot

Tau Ceti publishes **its own** oleans. Mathlib's come from Mathlib's cache, fetched by
`lake exe cache get`. So a tag guarantees that Tau Ceti's own library is cached for that
commit, and inherits whatever Mathlib published for the pin.

That matters for the releases Mathlib cut on its `stable` branch, `v4.29.1`, `v4.32.1` and
`v4.32.2`. Mathlib gates cache publication on a push to `master`, and a toolchain bump
invalidates every module hash, so `v4.32.0`'s cache does not carry over. **A consumer of
those tags must compile Mathlib themselves, whatever we publish**, and the release
workflow refuses to start such a build unless it is dispatched with
`allow_mathlib_rebuild`. That is upstream's gap and it cannot be closed from here.

## How the pieces fit

| Piece | What it does |
|---|---|
| `scripts/toolchain_tags.py` | The policy. Audits, names the target commit for each release, materialises a release commit's two pin files, and reports gaps to Zulip. Never builds, pushes or tags. |
| `.github/workflows/toolchain-tags.yml` | Runs the audit daily and reconciles the outstanding releases against Zulip. |
| `scripts/check-release-commit.sh`, `scripts/release_commit.py` | The trust anchor. Decides whether a commit may be built unsandboxed and published. Deliberately independent of the constructor above, so a bug there cannot certify itself. |
| `.github/workflows/release-tag.yml` | Builds one commit from source, publishes it, reads the publish back, and tags. Dispatched per release. |
| `.github/workflows/release-backfill.yml` | Runs the above over the audit's worklist, one release at a time. |

## Two things about the cache that are easy to get wrong

**The scope carries a platform for older releases.** Lake leaves the platform out of a
package's cache scope only when the lakefile declares `platformIndependent = true`. Tau
Ceti declared it on 2026-07-27; every release older than that is scoped
`<repo>/pt/x86_64-unknown-linux-gnu/tc/<toolchain>/<rev>` instead of
`<repo>/tc/<toolchain>/<rev>`. The publish job passes `--platform` exactly when the target
needs it, which is why the staging step in `release-tag.yml` reports platform dependence
where `ci.yml`'s copy fails on it: `ci.yml` only ever builds `main`, where its absence
would mean somebody had removed it.

**The uploading Lake is not the target's Lake.** `lake cache put-staged` gained `--rev`
and `--service` only in v4.34.0-rc1, so an older release's own Lake cannot be told which
revision to publish under. The publish job installs a modern toolchain as the uploader and
passes the target's toolchain as data through `--toolchain`.

## Keeping `main` from stepping over a release

Mathlib's `vX` tag sits on the commit that bumps its own `lean-toolchain` to `X`, so the
window in which `main` could pin it is exactly one Mathlib toolchain era, and for a stable
release that can be as little as fifteen hours. The daily bump takes the latest
last-known-good commit and has already stepped clean over one release that way
(`v4.33.0`). `update.yml` therefore pins a release tag as its own stepping stone before
continuing, so the exact commit exists on `main` rather than having to be constructed
afterwards.

That mechanism cannot reach the `stable`-branch patch releases, and structurally so:
`scripts/check-bump.sh` requires the Mathlib rev to be on the branch the lakefile
nominates, so a bump pinning one could never merge. They are backfill-only by
construction.
