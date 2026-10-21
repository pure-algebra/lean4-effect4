#!/bin/sh
# Run after the original review's audit.sh, with the same private TMPDIR.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
WORK=${TMPDIR:-/tmp}/effect4-host-runtime-audit
cd "$ROOT"
export LEAN_NUM_THREADS=3
mkdir -p "$WORK/src/Refinement" "$WORK/olean/Refinement"
lake build Test.Api.TypedReplies
MODULES=""
for pair in guard:Guard session:Session transcript:Transcript; do
  file=${pair%%:*}
  name=${pair##*:}
  lake env sh -c "LEAN_PATH=$WORK/olean:\$LEAN_PATH lean -DwarningAsError=true $HERE/probe-$file.lean"
  echo "ran clean: probe-$file.lean"
  cp "$HERE/probe-$file.lean" "$WORK/src/Refinement/$name.lean"
  lake env sh -c "LEAN_PATH=$WORK/olean:\$LEAN_PATH lean -DwarningAsError=true -R $WORK/src -o $WORK/olean/Refinement/$name.olean $WORK/src/Refinement/$name.lean"
  MODULES="$MODULES Refinement.$name"
done
{
  echo "import ProofGraph.AxiomAudit"
  for m in $MODULES; do echo "import $m"; done
  echo "#axiom_audit$MODULES"
} > "$WORK/src/Refinement/Audit.lean"
lake env sh -c "LEAN_PATH=$WORK/olean:\$LEAN_PATH lean -DwarningAsError=true $WORK/src/Refinement/Audit.lean"
