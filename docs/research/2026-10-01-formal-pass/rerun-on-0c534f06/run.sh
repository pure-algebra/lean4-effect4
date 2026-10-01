#!/bin/bash
# Rerun the formal pass's load-bearing probes on the merged tree (0c534f06), one at a time.
S=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad
F=/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-formal-pass
cd /Users/pooks/Dev/lean4-effect4
for p in algebra/probes/P2KripkeTyping algebra/verify-StepLoop proofs/probes/StaleCode proofs/verify-probes/VerifyAwaitLoad proofs/verify-probes/VerifySplit types/M5CounterProbe types/verify-CapstoneProbe types/verify-AmendedFitsProbe organization/verify-ExitOkOverload; do
  n=$(basename $p)
  start=$(date +%s)
  lake env lean -M6144 -DwarningAsError=true "$F/$p.lean" > "$S/formal-rerun/$n.log" 2>&1
  code=$?
  end=$(date +%s)
  errs=$(grep -c "error" "$S/formal-rerun/$n.log")
  ax=$(grep -c "depends on axioms" "$S/formal-rerun/$n.log")
  bad=$(grep -c "sorryAx\|Classical.choice" "$S/formal-rerun/$n.log")
  echo "$n exit=$code secs=$((end-start)) errors=$errs axiomlines=$ax suspicious=$bad"
done
