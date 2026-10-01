#!/bin/bash
# Build the shared core's and the proofs' oleans, then check each probe file, all through the
# one-compiler lock.
# Usage: bash docs/research/2026-09-30-pass/fiberslice/run.sh [Probe.lean ...]
# With no arguments every probe runs. Each probe's output goes to logs/<name>.log; the exit
# code of each command is appended to that log and printed.
set -u
LOCK=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh
REPO=/Users/pooks/Dev/lean4-effect4
DIR=docs/research/2026-09-30-pass/fiberslice
cd "$REPO" || exit 2
mkdir -p "$DIR/.build/Research/Pass/FiberSlice" "$DIR/logs"
bash "$LOCK" lake env lean -M6144 -DwarningAsError=true -R "$DIR" \
  -o "$DIR/.build/Research/Pass/FiberSlice/Core.olean" \
  "$DIR/Research/Pass/FiberSlice/Core.lean" > "$DIR/logs/Core.log" 2>&1
code=$?
echo "exit $code" >> "$DIR/logs/Core.log"
echo "Core.lean: exit $code"
[ $code -eq 0 ] || exit $code
bash "$LOCK" env LEAN_PATH="$REPO/$DIR/.build" lake env lean -M6144 -DwarningAsError=true -R "$DIR" \
  -o "$DIR/.build/Research/Pass/FiberSlice/Proofs.olean" \
  "$DIR/Research/Pass/FiberSlice/Proofs.lean" > "$DIR/logs/Proofs.log" 2>&1
code=$?
echo "exit $code" >> "$DIR/logs/Proofs.log"
echo "Proofs.lean: exit $code"
[ $code -eq 0 ] || exit $code
probes=("$@")
[ ${#probes[@]} -eq 0 ] && probes=(LivePath.lean Sites.lean Typed.lean Replays.lean Holes.lean DeclLane.lean)
for p in "${probes[@]}"; do
  [ -f "$DIR/$p" ] || { echo "$p: missing"; continue; }
  LEAN_PATH="$REPO/$DIR/.build" bash "$LOCK" lake env lean -M6144 -DwarningAsError=true \
    "$DIR/$p" > "$DIR/logs/${p%.lean}.log" 2>&1
  code=$?
  echo "exit $code" >> "$DIR/logs/${p%.lean}.log"
  echo "$p: exit $code"
done
