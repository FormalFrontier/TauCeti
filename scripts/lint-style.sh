#!/usr/bin/env bash
# Run the source-based style checks over every TauCeti source file.
#
# lint-style treats its module arguments as import roots and lints only their imports. The
# library root TauCeti.lean is intentionally empty, so generate a temporary import-all module
# instead. It lives under .lake because that is the writable area in the PR build sandbox. Source
# discovery and validation are shared with lint-env.sh so the two whole-library checks cannot
# drift apart.
set -euo pipefail

lint_src="$(mktemp -d "$PWD/.lake/lint-style-src.XXXXXX")"
trap 'rm -rf "$lint_src"' EXIT
lint_module="$lint_src/TauCetiLint/All.lean"
mkdir -p "$(dirname "$lint_module")"

. scripts/source-modules.sh
tauceti_source_modules "$lint_src/files" "$lint_src/modules"
mapfile -d '' files < "$lint_src/files"
printf 'import TauCeti\n' > "$lint_module"
sed 's/^/import /' "$lint_src/modules" >> "$lint_module"
expected_imports=$((${#files[@]} + 1))
emitted_imports="$(grep -c '^import ' "$lint_module")"
if ((emitted_imports != expected_imports)); then
  echo 'lint-style: generated import root is incomplete; refusing to run.' >&2
  exit 1
fi

# Use the validated discovery list for the copyright/Authors audit. Keep going after a header
# failure so contributors also see Mathlib's text-style diagnostics in the same CI round.
status=0
if ! lake env lean --run scripts/HeaderStyle.lean "${files[@]}"; then
  status=1
fi

# TauCetiLint.All supplies every TauCeti/ import plus TauCeti itself, so the intentionally empty
# root also receives text checks. The TauCeti argument makes lint-style's package-root filter retain
# those imports, while contributing none of its own. The copyright audit is separate because the
# pinned Mathlib header linter is a command linter that skips modules absent from the empty root.
if ! LEAN_SRC_PATH="$lint_src${LEAN_SRC_PATH:+:$LEAN_SRC_PATH}" \
    lake exe lint-style "$@" TauCetiLint.All TauCeti; then
  status=1
fi

exit "$status"
