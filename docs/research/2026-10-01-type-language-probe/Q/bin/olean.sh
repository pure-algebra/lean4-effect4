#!/usr/bin/env bash
# Compile one probe module to an .olean the generators can import, one compiler at a time.
#   Q/bin/olean.sh <root dir> <file.lean>
# The module name is the file's path below <root> (lean -R). Outputs go to $QBUILD (default:
# a directory outside the worktree, so no build product is ever committed), which is appended
# to LEAN_PATH for every later step. Flags as the brief requires: one thread, warnings are errors.
set -euo pipefail
WT=/Users/pooks/Dev/lean4-effect4-probe-Q
QBUILD=${QBUILD:-/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/qbuild}
root=$(cd "$1" && pwd); file=$(cd "$(dirname "$2")" && pwd)/$(basename "$2")
rel=${file#$root/}; stem=${rel%.lean}
mkdir -p "$QBUILD/$(dirname "$stem")"
cd "$WT"
export LEAN_NUM_THREADS=1
LEAN_PATH="$QBUILD" lake env lean -R "$root" -DwarningAsError=true -M6144 \
  -o "$QBUILD/$stem.olean" -i "$QBUILD/$stem.ilean" "$file"
