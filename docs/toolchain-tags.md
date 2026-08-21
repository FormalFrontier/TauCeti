# Toolchain tags

Tau Ceti carries a plain `vX.Y.Z` tag for each Lean release, the way Mathlib does, so a
project on Lean v4.34.0 can check out `v4.34.0` here and get a tree that builds.

`scripts/toolchain_tags.py` is the authority on what exists, what does not, and what to do
about it. It prints the rule with its report, so nothing below is needed to act on a gap.

## The rule

**`vX` is the first commit on `main` whose `lean-toolchain` is `leanprover/lean4:X`.**

Mathlib puts its `vX` tag on the commit that bumps its own `lean-toolchain` to X, and
`scripts/check-bump.sh` requires this repository's toolchain to match Mathlib's at whatever
it pins. The first `main` commit on toolchain X therefore pins Mathlib at or after Mathlib's
`vX` tag. Finding every tag target means reading `lean-toolchain` at the few commits that
change it, and nothing else.

An earlier design aimed at *exact* Mathlib pins. That required constructing release commits
on their own branches, building them from source, and publishing their caches, and it did
not survive review. A pin a little past Mathlib's tag is not worth that much machinery; the
tag message gives the pin.

## What a tag promises

The commit is on that Lean toolchain, its post-merge CI passed, and its oleans are in the
Lake artifact cache, so a checkout builds without recompiling the library. Both facts are
checked before a tag is created, and neither needs a rebuild: `main` already did the work
and recorded it.

## What it does not cover

A release `main` never ran on gets no tag, and nothing here will construct one, but the
report still lists it as `unreachable` rather than leaving it out: an audit whose job is to
say which releases have no tag is not allowed to answer by omission. Today that is
`v4.33.0`, whose window on Mathlib master was fifteen hours and which the daily bump stepped
straight over, and the patch releases `v4.32.1` and `v4.32.2`, which Mathlib cut on its
`stable` branch and which `check-bump.sh` could never have let this repository pin at all.

Knowing which of those two it is matters. A stepped-over release is a near miss the bump
could avoid another day; a `stable`-branch release is permanently out of reach and no
amount of automation here will change that.

Such a release can still be tagged by hand, off a `main` commit, and `v4.33.0` was: one
commit off `afb1aacb`, the last `main` commit before the bump jumped, changing only the two
pin files so that no source differs from that commit. It was built from source against
mathlib v4.33.0, passes the audits, and its oleans were uploaded to the Lake cache by hand,
so a checkout of it builds without recompiling: verified from a fresh clone, 7439 targets
up to date in eighteen seconds.

Nothing publishes for a commit off `main` automatically, so that upload was a manual step
(`lake cache stage`, then `lake cache put-staged` from a modern Lake with `--rev` and
`--toolchain`, since v4.33.0's own Lake has neither flag). The report therefore asks the
cache rather than assuming: it calls such a tag `tagged`, says it was constructed by hand,
and says whether a cache was found. `--create` will never make one.

Releases older than `v4.33.0-rc1` are out of scope, because the Lake cache does not reach
back that far and a tag could not promise a usable one. That bound is `EARLIEST_RELEASE` in
the script; raise it if the cache is ever pruned, never lower it.

## Using it

```
python3 scripts/toolchain_tags.py                      # the report
python3 scripts/toolchain_tags.py --create v4.34.0     # one tag
python3 scripts/toolchain_tags.py --create --all       # every ready release
```

Run it after a bump lands on a new toolchain. There is no schedule, because every run of
`--create` leaves a permanent tag and nothing here is urgent enough to do unattended. Creating a tag needs a `gh` login with write access; the report needs only read.

Tags are never moved. If one disagrees with the rule, the tool reports it and stops; that
is a question for a human, and no instruction it prints will delete or force a tag.
