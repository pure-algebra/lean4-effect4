#!/bin/sh
# Build the probe modules (src/ProbeView/*.lean) into build/, then run the named checks
# (checks/NAME.lean), one Lean process at a time, from the repository root.
#
#   sh run.sh                      build the modules only
#   sh run.sh FastCheck LiveBench  build, then run those checks
set -eu
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
cd "$root"
export LEAN_NUM_THREADS=3
mkdir -p "$here/build/ProbeView"
for m in Fast Layout Retained Inc Live; do
  [ -f "$here/src/ProbeView/$m.lean" ] || continue
  lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$here/build\" lean -DwarningAsError=true -R \"$here/src\" -o \"$here/build/ProbeView/$m.olean\" \"$here/src/ProbeView/$m.lean\""
  echo "built ProbeView.$m"
done
for c in "$@"; do
  echo "== $c"
  lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$here/build\" lean \"$here/checks/$c.lean\""
done
