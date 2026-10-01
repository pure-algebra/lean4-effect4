#!/bin/bash
# Verifier of seat TREE: rerun every seat probe through the one-compiler lock, one at a time.
# Logs: verify-rerun-<name>.log beside this script; exit codes in verify-rerun-summary.txt.
D=/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-data-probe/tree
SERIAL=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh
SUM=$D/verify-rerun-summary.txt
: > "$SUM"
for p in TyBillProbe TyBillOutsideProbe TyBillPrivateProbe AlphabetBillProbe SchemaProbe RecordNested RecordSpine explore/E1Instruments explore/E2Eliminator explore/E3Case16Trace; do
  name=$(basename "$p")
  start=$(date +%s)
  bash "$SERIAL" lake env lean -M6144 -DwarningAsError=true "$D/$p.lean" > "$D/verify-rerun-$name.log" 2>&1
  code=$?
  end=$(date +%s)
  echo "$p exit=$code seconds=$((end-start)) finished=$(date '+%H:%M:%S')" >> "$SUM"
done
echo DONE >> "$SUM"
