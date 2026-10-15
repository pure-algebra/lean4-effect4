#!/bin/bash
# The codegen review's fifth slot session (2026-10-15): the agent's loop and the to-do's emitter,
# each run interpreted (as today) and with the core's native library loaded. Run through the slot:
#
#   /Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh bash docs/research/2026-10-15-codegen-review/probes/session5.sh OUT
set -u
OUT=${1:?usage: session5.sh OUT}
mkdir -p "$OUT"
cd /Users/pooks/Dev/lean4-effect4
NATIVE="--load-dynlib=.lake/packages/typescript/.lake/build/lib/libtypescript_TypeScript.dylib --load-dynlib=.lake/packages/hash/.lake/build/lib/libhash_Hash.dylib --load-dynlib=.lake/build/lib/libeffect4_Effect4.dylib"
REQ=docs/research/2026-10-13-agent-ergonomics-probe/requests.jsonl
step() {
  local name=$1; shift
  local t0=$(date +%s)
  "$@" > "$OUT/$name.log" 2>&1
  printf '%s\t%s\t%s\n' "$name" "$?" "$(( $(date +%s) - t0 ))" >> "$OUT/times.tsv"
}
printf 'step\tstatus\tseconds\n' > "$OUT/times.tsv"
step build lake build Drivers.Session $(python3 scripts/lean-imports.py apps/todo/EmitTodo.lean)
step session-interpreted bash -c "lake env lean -M4096 --run tools/Drivers/Session.lean < $REQ"
step session-native bash -c "lake env lean -M4096 $NATIVE --run tools/Drivers/Session.lean < $REQ"
step emit-todo-interpreted lake env lean -M4096 --run apps/todo/EmitTodo.lean "$OUT/todo" ./prelude.ts
step emit-todo-native lake env lean -M4096 $NATIVE --run apps/todo/EmitTodo.lean "$OUT/todo-native" ./prelude.ts
