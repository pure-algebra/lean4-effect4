#!/usr/bin/env bash
# Seat S Lean runner: compile one standalone probe with the tree's oleans, one thread, warnings as
# errors; log the command, the time and the exit code beside the probe's output.
# usage: compile.sh <probe.lean> <log-name>
set -u
root=/Users/pooks/Dev/lean4-effect4-probe-S
probe=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
log=$(cd "$(dirname "$0")/../logs" && pwd)/$2.log
cd "$root"
{
  echo "# probe: ${probe#$root/}"
  echo "# date: $(date -u +%FT%TZ)"
  echo "# command: LEAN_NUM_THREADS=1 lake env lean -M6144 -DwarningAsError=true ${probe#$root/}"
  echo "# toolchain: $(cat lean-toolchain)"
  echo "# sha256: $(shasum -a 256 "$probe" | cut -d' ' -f1)"
} > "$log"
start=$(date +%s)
LEAN_NUM_THREADS=1 lake env lean -M6144 -DwarningAsError=true "$probe" >> "$log" 2>&1
code=$?
end=$(date +%s)
echo "# exit=$code seconds=$((end-start))" >> "$log"
echo "$2 exit=$code seconds=$((end-start))"
