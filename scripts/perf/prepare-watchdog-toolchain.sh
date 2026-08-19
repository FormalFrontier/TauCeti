#!/usr/bin/env bash
# Build a read-only, toolchain-shaped directory whose bin/lean is the watchdog.
set -euo pipefail

if [ "$#" != 2 ]; then
  echo "usage: $0 DESTINATION REAL_LEAN" >&2
  exit 2
fi

destination=$1
real_lean=$(realpath "$2")
real_root=$("$real_lean" --print-prefix)
case "$destination" in
  /*) ;;
  *) echo "error: watchdog toolchain destination must be absolute" >&2; exit 2 ;;
esac
if [ -e "$destination" ] || [ -L "$destination" ]; then
  echo "error: watchdog toolchain destination already exists: $destination" >&2
  exit 2
fi
test -x "$real_lean"
test -d "$real_root/bin"

mkdir -p "$destination/bin"
for entry in "$real_root"/*; do
  name=${entry##*/}
  [ "$name" = bin ] || ln -s "$entry" "$destination/$name"
done
for entry in "$real_root/bin"/*; do
  name=${entry##*/}
  [ "$name" = lean ] || ln -s "$entry" "$destination/bin/$name"
done
ln -s "$real_lean" "$destination/bin/lean-real"
install -m 0755 "$(dirname "$0")/lean-watchdog.sh" "$destination/bin/lean"

# Prove both sides of Lake's contract before this directory enters landrun.
test "$("$destination/bin/lean" --print-prefix)" = "$destination"
test "$("$destination/bin/lean" --githash)" = "$("$real_lean" --githash)"
