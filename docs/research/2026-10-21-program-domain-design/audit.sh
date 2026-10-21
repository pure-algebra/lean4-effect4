#!/bin/sh
# Run every probe of this note, then audit their declarations with the gate's own walk.
#
#   docs/research/2026-10-21-program-domain-design/audit.sh
#
# Steps: run each probe with `lake env lean` (every warning an error); compile each as the module
# `Probe.<Name>` into a scratch directory; then `#axiom_audit` (`tools/ProofGraph/AxiomAudit.lean`)
# over those modules, which walks every declaration and fails on an axiom outside
# [propext, Quot.sound]. The probes do not import one another. `probe-closure.lean` runs and is
# not audited: its helpers are metaprograms over `Lean.Environment`, which reach `Classical.choice`
# through the toolchain, and it states no law.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
WORK=${TMPDIR:-/tmp}/effect4-program-domain-audit
rm -rf "$WORK"
mkdir -p "$WORK/src/Probe" "$WORK/olean/Probe"
cd "$ROOT"
export LEAN_NUM_THREADS=3
MODULES=""
lake env lean -DwarningAsError=true "$HERE/probe-closure.lean"
echo "ran clean: probe-closure.lean"
for pair in names:Names certificate:Certificate reading:Reading object:Object service:Service \
    record:Record inspect:Inspect; do
  file=${pair%%:*}
  name=${pair##*:}
  lake env lean -DwarningAsError=true "$HERE/probe-$file.lean"
  echo "ran clean: probe-$file.lean"
  cp "$HERE/probe-$file.lean" "$WORK/src/Probe/$name.lean"
  lake env lean -R "$WORK/src" -o "$WORK/olean/Probe/$name.olean" "$WORK/src/Probe/$name.lean"
  MODULES="$MODULES Probe.$name"
done
{
  echo "import ProofGraph.AxiomAudit"
  for m in $MODULES; do echo "import $m"; done
  echo "#axiom_audit$MODULES"
} > "$WORK/src/Probe/Audit.lean"
lake env sh -c "LEAN_PATH=$WORK/olean:\$LEAN_PATH lean $WORK/src/Probe/Audit.lean"
