#!/usr/bin/env bash
# Run one command from the worktree root, recording the command, its output and its exit code.
#   Q/bin/logrun.sh <log path relative to Q/logs> -- <command...>
# The worktree is fixed so a reset working directory never reaches the main checkout.
set -u
export LEAN_NUM_THREADS=1
WT=/Users/pooks/Dev/lean4-effect4-probe-Q
Q=$WT/docs/research/2026-10-01-type-language-probe/Q
log="$Q/logs/$1"; shift
[ "$1" = "--" ] && shift
mkdir -p "$(dirname "$log")"
cd "$WT" || exit 99
start=$(date +%s)
{
  printf '$ cd %s\n$' "$WT"
  printf ' %q' "$@"
  printf '\n# started %s (LEAN_NUM_THREADS=%s)\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "${LEAN_NUM_THREADS:-unset}"
} > "$log"
"$@" >> "$log" 2>&1
code=$?
end=$(date +%s)
printf '# exit=%s seconds=%s\n' "$code" "$((end-start))" >> "$log"
echo "exit=$code seconds=$((end-start)) log=${log#$WT/}"
exit $code
