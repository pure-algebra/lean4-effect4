#!/bin/bash
# The codegen review's third slot session (2026-10-15): the statement census alone, after the
# second session's run stopped at an unopened namespace. Run through the shared slot:
#
#   /Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh bash docs/research/2026-10-15-codegen-review/probes/session3.sh OUT
set -u
OUT=${1:?usage: session3.sh OUT}
mkdir -p "$OUT"
cd /Users/pooks/Dev/lean4-effect4
t0=$(date +%s)
lake env lean -M8192 docs/research/2026-10-15-codegen-review/probes/StatementProbe.lean > "$OUT/statements.log" 2>&1
echo "statements exit $? in $(( $(date +%s) - t0 )) s" >> "$OUT/statements.log"
