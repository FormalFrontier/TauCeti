#!/usr/bin/env bash
# stage-lake-cache.sh — pack main's freshly built oleans and lay them out for the publish job.
#
# Runs INSIDE landrun, for the same reason the build does. Every `lake` invocation configures
# the workspace, and configuring elaborates each dependency's Lake config; at least one of them
# is a `lakefile.lean`, living under `.lake/packages`, which the sandboxed build can write. A
# `lake` run outside the sandbox would therefore elaborate whatever was left there, as the
# unrestricted runner user with $GITHUB_ENV, $GITHUB_PATH, $RUNNER_TEMP and the network in
# reach. Nothing in this file may move back out of the sandbox for that reason alone.
#
# Everything it produces lands under `.lake/staging`, the one writable directory this call is
# given beyond the build's own, and
# is therefore attacker-choosable: publish-lake-cache validates the staged tree before pointing
# Lake at it, and cross-checks the toolchain below against the `lean-toolchain` pin it reads for
# itself. Neither is a formality.
#
# cwd on entry is the workspace root. ci.yml is the only caller.
set -euxo pipefail

export TMPDIR="$PWD/.lake/tmp"

# Same watchdog wrapper the build used. Not for safety here, but so Lake sees the identical
# compiler and its traces still match: a different LEAN would make the packing build below
# recompile the library rather than pack it.
test -n "${WATCHDOG_TOOLCHAIN:-}"
test -x "$WATCHDOG_TOOLCHAIN/bin/lean"
export LAKE_OVERRIDE_LEAN=true
export LEAN="$WATCHDOG_TOOLCHAIN/bin/lean"

# Pack the already-built oleans into the local Lake cache. No recompile: the build left matching
# traces. Then emit the root-package input-to-output mappings and copy exactly the artifacts
# those mappings name into a staging directory beside them. `lake cache stage` reads no
# credential and contacts no network.
lake build >/dev/null
lake build --no-build -o .lake/staging/outputs.jsonl
echo "root-package mapping entries: $(wc -l < .lake/staging/outputs.jsonl)"
lake cache stage .lake/staging/outputs.jsonl .lake/staging/cache-staging

# `lake env` reports the workspace's own view of the toolchain, which is exactly the
# `Env.toolchain` Lake scopes an upload by. Recording it lets publish-lake-cache turn a
# disagreement with the `lean-toolchain` pin into a loud failure instead of a silently wrong
# upload scope. It reads this as untrusted input, which is the point: a wrong value fails that
# job rather than steering it.
lake env printenv ELAN_TOOLCHAIN > .lake/staging/toolchain.txt
