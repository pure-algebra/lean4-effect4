#!/bin/sh
# Run the two review probes against the design note's compiled probes, then audit their
# declarations with the gate's own walk (`#axiom_audit`, `tools/ProofGraph/AxiomAudit.lean`).
#
#   docs/research/2026-10-21-host-runtime-review/audit.sh > docs/research/2026-10-21-host-runtime-review/audit.out
#
# Step 1 runs the design note's `audit.sh`, which compiles its probes as the modules
# `Probe.Host`, `Probe.Run`, `Probe.Session` and `Probe.Deploy` into a scratch directory. Step 2
# runs each review probe (every warning an error) with those modules on the path, compiles it as
# `Review.<Name>`, and audits the two review modules.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
DESIGN="$ROOT/docs/research/2026-10-21-host-runtime-design"
WORK=${TMPDIR:-/tmp}/effect4-host-runtime-audit
cd "$ROOT"
export LEAN_NUM_THREADS=3
sh "$DESIGN/audit.sh"
mkdir -p "$WORK/src/Review" "$WORK/olean/Review"
MODULES=""
for pair in guard:Guard transcript:Transcript; do
  file=${pair%%:*}
  name=${pair##*:}
  lake env sh -c "LEAN_PATH=$WORK/olean:\$LEAN_PATH lean -DwarningAsError=true $HERE/probe-$file.lean"
  echo "ran clean: probe-$file.lean"
  cp "$HERE/probe-$file.lean" "$WORK/src/Review/$name.lean"
  lake env sh -c "LEAN_PATH=$WORK/olean:\$LEAN_PATH lean -R $WORK/src -o $WORK/olean/Review/$name.olean $WORK/src/Review/$name.lean"
  MODULES="$MODULES Review.$name"
done
{
  echo "import ProofGraph.AxiomAudit"
  for m in $MODULES; do echo "import $m"; done
  echo "#axiom_audit$MODULES"
} > "$WORK/src/Review/Audit.lean"
lake env sh -c "LEAN_PATH=$WORK/olean:\$LEAN_PATH lean $WORK/src/Review/Audit.lean"
