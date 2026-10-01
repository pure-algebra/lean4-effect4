#!/bin/bash
# The producer chain in the fixed order, LEAN_NUM_THREADS=1, each logged with its exit code.
SP=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/d4
cd /Users/pooks/Dev/lean4-effect4-seat-D4 || exit 99
export LEAN_NUM_THREADS=1
for fam in derived lcnf eff wire cas; do
  start=$(date +%s)
  python3 scripts/generate.py --only $fam > $SP/logs/gen-$fam.log 2>&1
  code=$?
  end=$(date +%s)
  echo "gen-$fam exit=$code seconds=$((end-start))" | tee -a $SP/logs/chain.summary
  git status --short --untracked-files=no -- ocaml src tools ts harness generated >> $SP/logs/chain.summary
  if [ $code -ne 0 ]; then exit $code; fi
done
echo "chain done" >> $SP/logs/chain.summary
