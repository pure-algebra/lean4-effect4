#!/bin/bash
# Seat R's one compile command: one probe, one thread, warnings as errors, from the worktree
# root; writes <probe>.log beside it with the exit code and wall seconds appended. Extra
# arguments after the file (e.g. -M6144) are passed to lean before the file.
#   bash docs/research/2026-10-01-type-language-probe/R/run-lean.sh <path/to/Probe.lean> [lean flags]
set -u
f="$1"
shift
log="${f%.lean}.log"
cd /Users/pooks/Dev/lean4-effect4-probe-R || exit 2
start=$(date +%s)
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true "$@" "$f" > "$log" 2>&1
code=$?
end=$(date +%s)
echo "exit=$code seconds=$((end - start))" >> "$log"
cat "$log"
exit $code
