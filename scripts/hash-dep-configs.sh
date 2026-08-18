#!/usr/bin/env bash
# hash-dep-configs.sh — checksum the Lake config of every dependency, for the tripwire in ci.yml.
#
# The filenames come from lake-manifest.json's `configFile` for each package rather than a
# `lakefile.*` glob, so a dependency naming its config something else is still covered. The
# manifest itself is checked too: rewriting it to point at a different config would otherwise move
# the tripwire rather than trip it. It is a repository file, outside the sandbox's writable mount.
#
# This is a canary for crude persistent edits. It cannot see a poisoned compiled config, a helper
# imported by a lakefile, or a modify-run-restore sequence. ci.yml says so where it is used.
#
# Prints "<sha256>  <path>" per existing file, sorted by path. Paths that do not exist are skipped
# rather than failing: a dependency's lakefile.olean is absent until something compiles it, and
# their appearance or disappearance is itself a difference the caller's diff will show.
set -euo pipefail

configs() {
  python3 - <<'PY'
import json

manifest = json.load(open("lake-manifest.json"))
for pkg in manifest.get("packages", []):
    name = pkg.get("name")
    if not name:
        continue
    # `configFile` is optional; Lake's own default applies when it is absent.
    config = pkg.get("configFile") or "lakefile.toml"
    print(f".lake/packages/{name}/{config}")
    # The compiled form, which Lake elaborates in preference to the source when it is current.
    print(f".lake/packages/{name}/.lake/lakefile.olean")
PY
}

{
  sha256sum lake-manifest.json
  # A plain `if`, never `[ -e "$rel" ] && sha256sum "$rel"`. Under `set -e` a loop takes the exit
  # status of its final iteration, so the `&&` form aborts the whole script whenever the last path
  # happens not to exist, which is precisely what an uncompiled lakefile.olean does.
  while IFS= read -r rel; do
    if [ -e "$rel" ]; then
      sha256sum "$rel"
    fi
  done < <(configs)
} | sort -k2
