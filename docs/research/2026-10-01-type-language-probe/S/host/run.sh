#!/usr/bin/env bash
# Seat S host runner: run one command from this folder, log versions, the command and the exit.
# usage: ./run.sh <log-name> <command...>
set -u
cd "$(dirname "$0")"
name=$1; shift
log="logs/$name.log"
{
  echo "# check: $name"
  echo "# date: $(date -u +%FT%TZ)"
  echo "# cwd: $(pwd)"
  echo "# command: $*"
  echo "# versions: bun $(bun --version); tsgo $(/opt/homebrew/bin/tsgo --version | sed 's/Version //'); node $(node --version)"
} > "$log"
start=$(date +%s)
"$@" >> "$log" 2>&1
code=$?
end=$(date +%s)
echo "# exit=$code seconds=$((end-start))" >> "$log"
echo "$name exit=$code"
exit 0
