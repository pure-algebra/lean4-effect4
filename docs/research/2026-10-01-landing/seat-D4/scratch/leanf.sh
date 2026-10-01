#!/bin/bash
# leanf.sh <tag> <file> : lake env lean -DwarningAsError=true on one file in the seat-D4 worktree, logged
tag=$1; file=$2
log=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/d4/logs/$tag.log
cd /Users/pooks/Dev/lean4-effect4-seat-D4 || exit 99
start=$(date +%s)
LEAN_NUM_THREADS=4 lake env lean -M6144 -DwarningAsError=true "$file" > "$log" 2>&1
code=$?
end=$(date +%s)
echo "exit=$code seconds=$((end-start)) log=$log"
exit $code
