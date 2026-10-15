#!/bin/bash
# The codegen review's fourth slot session (2026-10-15): the type-spelling probe. Run through the
# shared slot:
#
#   /Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh bash docs/research/2026-10-15-codegen-review/probes/session4.sh OUT
set -u
OUT=${1:?usage: session4.sh OUT}
mkdir -p "$OUT"
cd /Users/pooks/Dev/lean4-effect4
t0=$(date +%s)
lake env lean -M4096 docs/research/2026-10-15-codegen-review/probes/TypeSpellings.lean > "$OUT/types.log" 2>&1
echo "types exit $? in $(( $(date +%s) - t0 )) s" >> "$OUT/types.log"
