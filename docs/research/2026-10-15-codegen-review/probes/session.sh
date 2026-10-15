#!/bin/bash
# The codegen review's one slot session (2026-10-15): one build of what the probes import, then
# every Lean measurement, each timed. Run from anywhere, through the shared slot:
#
#   /Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh bash docs/research/2026-10-15-codegen-review/probes/session.sh OUT
#
# It writes logs under OUT only (a scratch directory). It edits no tracked file: every producer
# writes into OUT, and the two gate scripts it times write their work under ignored folders.
set -u
ROOT=/Users/pooks/Dev/lean4-effect4
OUT=${1:?usage: session.sh OUT}
mkdir -p "$OUT"
cd "$ROOT"
TS_LIB=.lake/packages/typescript/.lake/build/lib/libtypescript_TypeScript.dylib
HASH_LIB=.lake/packages/hash/.lake/build/lib/libhash_Hash.dylib
CORE_LIB=.lake/build/lib/libeffect4_Effect4.dylib
NATIVE="--load-dynlib=$TS_LIB --load-dynlib=$HASH_LIB --load-dynlib=$CORE_LIB"

step() {
  # step NAME COMMAND...: run, time and log one command; never stop the session
  local name=$1; shift
  local t0=$(date +%s)
  echo "== $name: $*" >> "$OUT/steps.log"
  "$@" > "$OUT/$name.log" 2>&1
  local status=$?
  local t1=$(date +%s)
  printf '%s\t%s\t%s\n' "$name" "$status" "$((t1 - t0))" >> "$OUT/times.tsv"
}

printf 'step\tstatus\tseconds\n' > "$OUT/times.tsv"
echo "session start $(date -u +%FT%TZ) at $(git rev-parse HEAD)" > "$OUT/steps.log"

# 1. One build: the registry's roots, the proof-graph tools, the report, the codegen drivers, and
#    the native libraries the drivers can load.
step build lake build Effect4.Laws Test.Program.TypedProgBindRed \
  Test.Dogfood.P1HttpCache Test.Dogfood.P2HandlerLayers Test.Dogfood.P3WorkerQueue \
  Test.Dogfood.P4RateLimiter Test.Dogfood.P5LedgerService Test.Dogfood.Scenario \
  Test.Dogfood.Scenario.Workers Test.Dogfood.Scenario.Routing Test.Dogfood.Scenario.Atomic \
  Test.Dogfood.Scenario.Timeout Test.Dogfood.Scenario.Tape Test.Dogfood.Scenario.QueueWorkers \
  Test.Dogfood.Bank Test.Dogfood.Scenario.Todo.Claims Test.Dogfood.Scenario.Todo.Cached \
  Tools.View.FlowReach Tools.LoadPaths ProofGraph.StatementCensus ProofGraph.AxiomAudit \
  semantics-report Drivers.Corpus Drivers.TsGen Drivers.Emit Tools.RowTypes Tools.TyVectors \
  $(python3 scripts/lean-imports.py harness/truth/Truth.lean harness/truth/schema-codec/Emit.lean \
    harness/schema-generation/EmitFixture.lean harness/truth/P2b.lean) \
  @typescript/TypeScript:shared @hash/Hash:shared Effect4:shared

# 2. The proof graph at HEAD.
step semantics lake exe semantics-report "$OUT/semantics-report"
step probe lake env lean -M8192 docs/research/2026-10-15-codegen-review/probes/ProofGraphProbe.lean

# 3. The codegen's Lean producers, each into OUT: interpreted (as the Makefile runs them), then
#    with the native libraries loaded (as the fixtures lane runs its writers).
step corpus-interpreted lake env lean -M4096 --run tools/Drivers/Corpus.lean "$OUT/corpus" 400 4
step corpus-native lake env lean -M4096 $NATIVE --run tools/Drivers/Corpus.lean "$OUT/corpus-native" 400 4
step tsgen-interpreted lake env lean -M4096 --run tools/Drivers/TsGen.lean "$OUT/ts"
step tsgen-native lake env lean -M4096 $NATIVE --run tools/Drivers/TsGen.lean "$OUT/ts-native"
step truth-interpreted lake env lean -M4096 --run harness/truth/Truth.lean "$OUT/truth-corpus.json" --tapes harness/truth/tapes
step truth-native lake env lean -M4096 $NATIVE --run harness/truth/Truth.lean "$OUT/truth-corpus-native.json" --tapes harness/truth/tapes
step truth-manifest-interpreted lake env lean -M4096 --run harness/truth/Truth.lean --corpus "$OUT/corpus-manifest.json" 400 4
step emit-interpreted lake env lean -M4096 --run tools/Drivers/Emit.lean "$OUT/emit"
step rowtypes-check lake env lean -M4096 --run tools/Tools/RowTypes.lean generated/row-types.tsv --check
step tyvectors lake env lean -M4096 --run tools/Tools/TyVectors.lean "$OUT/ty-vectors.tsv"
step schema-codec-emit lake env lean -M4096 --run harness/truth/schema-codec/Emit.lean "$OUT/schema-values.ts"
step schema-ts-emit lake env lean -M4096 harness/schema-generation/EmitFixture.lean

# 4. The whole truth and corpus gates, as their scripts run them (each writes under an ignored
#    work folder and compares with the committed files).
step check-truth python3 scripts/check-truth.py
step check-corpus python3 scripts/check-corpus.py

echo "session end $(date -u +%FT%TZ)" >> "$OUT/steps.log"
