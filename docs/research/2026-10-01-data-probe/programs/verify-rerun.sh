#!/bin/bash
# Verifier of seat PROGRAMS (second instance; the first instance's run was terminated mid-ProbeBill):
# rerun the seat's six Lean probes, one at a time, through the one-compiler lock, with the seat's
# own command. Logs go beside this script as verify-rerun-<probe>.log; exit codes and seconds in
# verify-rerun-summary.txt.
S=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh
D=/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-data-probe/programs
: > $D/verify-rerun-summary.txt
for p in ProbeTodayP2 ProbeRedControls ProbeSpine ProbeRecordK2 RedMustFail ProbeBill; do
  start=$(date +%s)
  bash $S lake env lean -M6144 -DwarningAsError=true $D/$p.lean > $D/verify-rerun-$p.log 2>&1
  code=$?
  echo "$p exit=$code seconds=$(( $(date +%s) - start ))" >> $D/verify-rerun-summary.txt
done
echo done >> $D/verify-rerun-summary.txt
