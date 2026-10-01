#!/bin/bash
# build.sh <tag> <modules...> : LEAN_NUM_THREADS=4 lake build in the seat-D4 worktree, logged
tag=$1; shift
log=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/d4/logs/$tag.log
cd /Users/pooks/Dev/lean4-effect4-seat-D4 || exit 99
start=$(date +%s)
LEAN_NUM_THREADS=4 lake build "$@" > "$log" 2>&1
code=$?
end=$(date +%s)
echo "exit=$code seconds=$((end-start)) log=$log"
exit $code
