#!/usr/bin/env bash
# Seat G: run one command in the seat-G worktree, log its output, exit code and wall time.
# Usage: run.sh <log-name> <command...>   (log at seat-G/logs/<log-name>.log)
set -u
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../../.." && pwd)"
log="$here/logs/$1.log"; shift
cd "$root" || exit 2
start=$(date +%s)
LEAN_NUM_THREADS=4 "$@" > "$log" 2>&1
ec=$?
echo "## exit=$ec seconds=$(( $(date +%s) - start )) cmd=LEAN_NUM_THREADS=4 $* head=$(git rev-parse --short HEAD) dirty=$(git status --porcelain --untracked-files=no | wc -l | tr -d ' ')" >> "$log"
tail -n 1 "$log"
exit $ec
