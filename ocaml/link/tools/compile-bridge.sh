#!/usr/bin/env bash
# tools/compile-bridge.sh — Bridge.lean -> Bridge.c -> Bridge.o, in $E4_OUT (Linux side).
#
#   bash tools/compile-bridge.sh           # only if Bridge.lean differs from the last compiled copy
#   bash tools/compile-bridge.sh --force   # always
#
# The source is the repo's `src/OCaml5/Bridge.lean` ($E4_BRIDGE_SRC, the coordinator's
# file); it is copied to $E4_OUT/Bridge.lean, so the compiled module is `Bridge` and the
# symbol `initialize_Bridge` is the one e4_stubs.c declares.
#
# One lean process, capped at 4 GB (-M4096). A failed compile leaves no Bridge.o behind, so
# the next run recompiles. The static libraries of the Linux tree are built on demand
# (`lake build …:static`) only when one is missing.
set -euo pipefail
source "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)/lean-env.sh"
mkdir -p "$E4_OUT"
src="$E4_BRIDGE_SRC"
copy="$E4_OUT/Bridge.lean"
if [ "${1:-}" != "--force" ] && [ -f "$E4_OUT/Bridge.o" ] && cmp -s "$src" "$copy"; then
  echo "--- Bridge.o is current ($E4_OUT/Bridge.o)"
else
  rm -f "$E4_OUT/Bridge.o" "$E4_OUT/Bridge.c" "$E4_OUT/Bridge.olean"
  cp "$src" "$copy"
  cd "$E4_OUT"
  echo "--- Bridge.lean -> Bridge.c -> Bridge.o (lean -M4096, one process)"
  lean -M4096 -o Bridge.olean -c Bridge.c Bridge.lean
  leanc -c -O3 -o Bridge.o Bridge.c
  echo "--- Bridge.o: $(stat -c %s Bridge.o) bytes"
fi

missing=0
for lib in $(e4_lean_libs); do
  [ -f "$lib" ] || { echo "  MISSING $lib"; missing=1; }
done
if [ "$missing" = 1 ]; then
  echo "--- static libraries: building the missing ones in $E4_LEAN_REPO"
  ( cd "$E4_LEAN_REPO" && lake build Effect4:static effects/Effects:static typescript/TypeScript:static hash/Hash:static 2>&1 | tail -3 )
  for lib in $(e4_lean_libs); do
    [ -f "$lib" ] || { echo "  STILL MISSING $lib"; exit 1; }
  done
fi
