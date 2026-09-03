#!/usr/bin/env bash
# Shared, fail-closed discovery of the Lean modules under TauCeti/.
#
# tauceti_source_modules FILES MODULES writes the validated source paths as a
# NUL-delimited list to FILES and the corresponding Lean module names, one per
# line, to MODULES. Callers choose their own temporary destinations.

tauceti_source_modules() {
  local files_out="$1"
  local modules_out="$2"
  local symlinks_out="${files_out}.symlinks"
  local module_path_re="^TauCeti(/[A-Za-z_][A-Za-z0-9_']*)+\.lean$"
  local file module
  local -a files=()
  local -a symlinks=()

  find TauCeti -type f -name '*.lean' -print0 | LC_ALL=C sort -z > "$files_out"
  find TauCeti -type l -print0 | LC_ALL=C sort -z > "$symlinks_out"
  mapfile -d '' files < "$files_out"
  mapfile -d '' symlinks < "$symlinks_out"
  if ((${#symlinks[@]} != 0)); then
    printf 'source-modules: refusing symlinked source path %q\n' "${symlinks[0]}" >&2
    return 1
  fi
  if ((${#files[@]} == 0)); then
    echo 'source-modules: found no TauCeti source files; the audit is miswired.' >&2
    return 1
  fi

  : > "$modules_out"
  for file in "${files[@]}"; do
    if [[ ! $file =~ $module_path_re ]]; then
      printf 'source-modules: refusing non-module source path %q\n' "$file" >&2
      return 1
    fi
    module="${file%.lean}"
    printf '%s\n' "${module//\//.}" >> "$modules_out"
  done
}
