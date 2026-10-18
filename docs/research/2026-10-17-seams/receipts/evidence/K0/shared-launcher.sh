#!/bin/bash
# Run "$@" holding one of two Lean slots shared by every seat of the 2026-10-04 night.
# Two slots of two threads each keep the machine out of swap (AGENTS.md: one lake per
# worktree, LEAN_NUM_THREADS bounded). A slot whose holder died is reclaimed.
export PATH="/Users/pooks/.elan/bin:$PATH"
D=/Users/pooks/Dev/lean4-effect4/scratch/locks
while true; do
  for s in 0 1; do
    if mkdir "$D/slot$s" 2>/dev/null; then
      echo $$ > "$D/slot$s/pid"
      trap "rm -rf '$D/slot$s'" EXIT INT TERM
      export LEAN_NUM_THREADS=2
      "$@"
      exit $?
    fi
    pid=$(cat "$D/slot$s/pid" 2>/dev/null)
    if [ -n "$pid" ] && ! kill -0 "$pid" 2>/dev/null; then rm -rf "$D/slot$s"; fi
  done
  sleep 3
done
