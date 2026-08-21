# Toolchain tags

Tau Ceti tags eligible Lean releases as `vX`, the way Mathlib does, so a project on Lean
v4.34.0 can check out `v4.34.0` here and get a tree that builds.

## The rule

**`vX` is the first commit on `main` whose `lean-toolchain` is `leanprover/lean4:X`.**

Mathlib puts its `vX` tag on the commit that bumps its own `lean-toolchain` to X, and
`scripts/check-bump.sh` requires this repository's toolchain to match Mathlib's at whatever
it pins. The first `main` commit on toolchain X therefore pins Mathlib at or after Mathlib's
`vX` tag. The tag message gives the pin.

Exact Mathlib pins were tried and dropped: they need release commits constructed on their
own branches, built from source, and their caches published.

## What a tag promises

The commit is on that Lean toolchain, its post-merge CI passed, and its oleans are in the
Lake artifact cache, so a checkout builds without recompiling the library. The tool checks
the recorded CI result and the published cache; neither needs a rebuild.

## What it does not cover

The tool tags only commits on `main`, and reports a release `main` never ran on as
`unreachable`. Two things cause that, and they differ in what can be done about them: the
daily bump stepped over the release's window on Mathlib master, which a later bump could
avoid, or Mathlib cut the release on its `stable` branch, which `check-bump.sh` will not let
this repository pin at all.

Such a release can still be tagged by hand off a `main` commit. `v4.33.0` is one: a commit
off `afb1aacb` changing only the two pin files, built from source, with its cache uploaded
manually. The report marks it `tagged`, notes that it was constructed, and says whether it
found a cache. `--create` does not construct these; the procedure is in the module docstring
of `scripts/toolchain_tags.py`.

Releases older than `v4.33.0-rc1` are out of scope, because the Lake cache has no older
entries. That bound is `EARLIEST_RELEASE` in the script; raise it if the cache is pruned,
never lower it.

## Using it

```
python3 scripts/toolchain_tags.py                      # the report
python3 scripts/toolchain_tags.py --create v4.34.0     # one tag
python3 scripts/toolchain_tags.py --create --all       # every ready release
```

Run `--create` after a bump lands on a new toolchain. It needs a `gh` login with write
access; the report needs only read.

If a tag does not match the rule, the tool reports it and changes nothing.
