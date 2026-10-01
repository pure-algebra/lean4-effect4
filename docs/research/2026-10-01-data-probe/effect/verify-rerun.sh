#!/bin/bash
# Verifier rerun of seat EFFECT's six Lean probes, each through the one-compiler lock, one at a time.
# Logs: verify-rerun-<probe>.log beside this script. The seat's files are only read.
SERIAL=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh
D=/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-data-probe/effect
for p in ProbeCodecStatus ProbeRecordModel ProbeRed1_RecordReads ProbeRed2_ExactWithoutNormaliser ProbeRed3_ModelNeedsDistinctNames ProbeRed4_TsRuleNotMonotone; do
  start=$(date +%s)
  bash "$SERIAL" lake env lean -M6144 -DwarningAsError=true "$D/lean/$p.lean" > "$D/verify-rerun-$p.log" 2>&1
  rc=$?
  echo "exit=$rc elapsed=$(( $(date +%s) - start ))s (includes lock wait)" >> "$D/verify-rerun-$p.log"
done
echo done > "$D/verify-rerun.done"
