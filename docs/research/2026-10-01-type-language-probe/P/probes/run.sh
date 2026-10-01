#!/usr/bin/env bash
# Seat P probe builder: compiles each layer in order, one compiler at a time, with
# LEAN_NUM_THREADS=1 and -DwarningAsError=true, writing each layer's .olean into the session
# scratchpad (never the tree) so later layers import earlier ones.
# Usage: run.sh [Layer ...]   (default: every layer in order). Logs: logs/<Layer>.log
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="/Users/pooks/Dev/lean4-effect4-probe-P"
OLEAN="${PROBE_P_OLEAN:-/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/olean}"
mkdir -p "$OLEAN" "$HERE/logs"
LAYERS=("$@")
if [ ${#LAYERS[@]} -eq 0 ]; then
  LAYERS=(P1FieldOrder P2Ty P3View P4Algebra P4Check P5Fits P6Inhabited P7Tagged P8Codec P8Schema)
fi
cd "$ROOT"
for L in "${LAYERS[@]}"; do
  [ -f "$HERE/$L.lean" ] || { echo "skip $L (no file)"; continue; }
  start=$(date +%s)
  LEAN_NUM_THREADS=1 lake env sh -c "LEAN_PATH=\$LEAN_PATH:$OLEAN lean --root=$HERE -DwarningAsError=true -o $OLEAN/$L.olean $HERE/$L.lean" > "$HERE/logs/$L.log" 2>&1
  code=$?
  echo "exit=$code seconds=$(( $(date +%s) - start ))" >> "$HERE/logs/$L.log"
  echo "$L exit=$code ($(( $(date +%s) - start ))s)"
  [ $code -eq 0 ] || exit $code
done
