#!/bin/bash
# Verifier of seat ORGANIZATION: run one of my own probes (verify-*.lean) through the lock.
# Usage: bash verify-run.sh verify-Name   -> verify-logs/verify-Name.log (exit and seconds appended)
SER=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh
DIR=/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-formal-pass/organization
p=$1; f="$DIR/$p.lean"; log="$DIR/verify-logs/$p.log"
start=$(date +%s)
bash "$SER" lake env lean -M6144 -DwarningAsError=true "$f" > "$log" 2>&1
rc=$?
end=$(date +%s)
echo "## exit=$rc seconds=$((end-start)) probe=$f" >> "$log"
echo "$p exit=$rc seconds=$((end-start))" >> "$DIR/verify-logs/run-summary.log"
cat "$log" | head -c 20000
