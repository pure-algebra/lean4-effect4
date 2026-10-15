#!/bin/bash
# The codegen review's second slot session (2026-10-15): the statement census that the first
# session's probe stopped at, and the elaboration time of the codegen's heaviest modules, each
# re-elaborated from its built imports (the build of the first session restored these modules
# from Lake's cache, so it timed none of them). Run through the shared slot:
#
#   /Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh bash docs/research/2026-10-15-codegen-review/probes/session2.sh OUT
#
# It writes logs under OUT only. `lake env lean FILE` elaborates FILE and writes no olean.
set -u
ROOT=/Users/pooks/Dev/lean4-effect4
OUT=${1:?usage: session2.sh OUT}
mkdir -p "$OUT"
cd "$ROOT"

step() {
  local name=$1; shift
  local t0=$(date +%s)
  echo "== $name: $*" >> "$OUT/steps.log"
  "$@" > "$OUT/$name.log" 2>&1
  local status=$?
  local t1=$(date +%s)
  printf '%s\t%s\t%s\n' "$name" "$status" "$((t1 - t0))" >> "$OUT/times.tsv"
}

printf 'step\tstatus\tseconds\n' > "$OUT/times.tsv"
echo "session2 start $(date -u +%FT%TZ) at $(git rev-parse HEAD)" > "$OUT/steps.log"

step statements lake env lean -M8192 docs/research/2026-10-15-codegen-review/probes/StatementProbe.lean

# The elaboration time of the codegen's law modules and of its core modules, one at a time.
for m in Laws/Codegen/PrintTyped Laws/Codegen/ReadLeaf Laws/Codegen/ReadPrint Laws/Codegen/Module \
         Laws/Codegen/Definitions Laws/Codegen/Read Laws/Codegen/PrintReadable Laws/Codegen/Template \
         Laws/Codegen/Services Laws/Codegen/Admit Laws/Codegen/Mask Laws/Codegen/Forms \
         Codegen/Read Codegen/Print Codegen/Template Codegen/Types Codegen/PrintLeaf Codegen/Schema; do
  step "elab-$(echo $m | tr '/' '-')" lake env lean -M6144 "src/Effect4/$m.lean"
done

echo "session2 end $(date -u +%FT%TZ)" >> "$OUT/steps.log"
