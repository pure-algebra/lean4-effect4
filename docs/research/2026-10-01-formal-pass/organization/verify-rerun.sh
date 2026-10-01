#!/bin/bash
# Verifier of seat ORGANIZATION (2026-10-01): rerun the seat's Lean probes, one at a time,
# through the one-compiler lock; logs go to verify-logs/rerun-<Probe>.log with exit and seconds.
# Usage: bash verify-rerun.sh Probe1 Probe2 ...   (names without .lean, from ./probes/)
SER=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh
DIR=/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-formal-pass/organization
for p in "$@"; do
  f="$DIR/probes/$p.lean"; log="$DIR/verify-logs/rerun-$p.log"
  start=$(date +%s)
  bash "$SER" lake env lean -M6144 -DwarningAsError=true "$f" > "$log" 2>&1
  rc=$?
  end=$(date +%s)
  echo "## exit=$rc seconds=$((end-start)) probe=$f" >> "$log"
  echo "$p exit=$rc seconds=$((end-start))" >> "$DIR/verify-logs/rerun-summary.log"
done
