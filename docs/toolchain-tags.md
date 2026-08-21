# Toolchain tags

Tau Ceti carries a plain `vX.Y.Z` tag for each Lean release, the way Mathlib does, so a
project on Lean v4.34.0 can check out `v4.34.0` here and get a tree that builds.

`scripts/toolchain_tags.py` is the authority on what exists, what does not, and what to do
about it. It prints the rule with its report, so nothing below is needed to act on a gap.

## The rule

**`vX` is the first commit on `main` whose `lean-toolchain` is `leanprover/lean4:X`.**

That is the whole policy, and it is deliberately not cleverer than that.

It gives the property worth having for free. Mathlib puts its own `vX` tag on the commit
that bumps its `lean-toolchain` to X, and `scripts/check-bump.sh` already forces this
repository's toolchain to equal Mathlib's at whatever it pins. So the first `main` commit
on toolchain X necessarily pins Mathlib at or after Mathlib's own `vX` tag. Nothing has to
compute that, compare pins, derive a base, or ask Mathlib anything: reading `lean-toolchain`
at the handful of commits that change it is enough to find every tag target.

An earlier design chased *exact* Mathlib pins, which meant constructing release commits on
their own branches, building them from source, and publishing their caches, none of which
survived review. The pin being a little past Mathlib's tag is not worth that machinery. The
tag message records the pin so a reader can see for themselves.

## What a tag promises

The commit is on that Lean toolchain, its post-merge CI passed, and its oleans are in the
Lake artifact cache, so a checkout builds without recompiling the library. Both facts are
checked before a tag is created, and neither needs a rebuild: `main` already did the work
and recorded it.

## What it does not cover

A release `main` never ran on gets no tag, and nothing here will construct one. Today that
is `v4.33.0`, whose window on Mathlib master was fifteen hours and which the daily bump
stepped straight over, and the patch releases `v4.32.1` and `v4.32.2`, which Mathlib cut on
its `stable` branch and which `check-bump.sh` could never have let this repository pin.

Releases older than `v4.33.0-rc1` are out of scope, because the Lake cache does not reach
back that far and a tag could not promise a usable one. That bound is `EARLIEST_RELEASE` in
the script; raise it if the cache is ever pruned, never lower it.

## Using it

```
python3 scripts/toolchain_tags.py                      # the report
python3 scripts/toolchain_tags.py --create v4.34.0     # one tag
python3 scripts/toolchain_tags.py --create --all       # every ready release
```

Run it after a bump lands on a new toolchain. It is deliberately not on a schedule: every
run of `--create` leaves a permanent tag, and there is no hurry that justifies making that
unattended. Creating a tag needs a `gh` login with write access; the report needs only read.

Tags are never moved. If one disagrees with the rule, the tool reports it and stops; that
is a question for a human, and no instruction it prints will delete or force a tag.
