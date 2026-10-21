#!/bin/sh
# Run every probe of this note against a checkout of `codex/program-domain`, then audit their
# declarations with the gate's own walk (`#axiom_audit`, `tools/ProofGraph/AxiomAudit.lean`).
#
#   docs/research/2026-10-21-program-domain-review/audit.sh <checkout of codex/program-domain>
#
# The probes import the landed modules (`Effect4.Laws.Api.Object`, `Effect4.Api.Author`,
# `Effect4.Laws.Codegen.Services`), so the checkout must hold the landing. Every warning is an
# error. The probes do not import one another.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "${1:?checkout of codex/program-domain}" && pwd)
WORK=${TMPDIR:-/tmp}/effect4-program-domain-review-audit
rm -rf "$WORK"
mkdir -p "$WORK/src/Probe" "$WORK/olean/Probe"
cd "$ROOT"
export LEAN_NUM_THREADS=3
MODULES=""
for pair in exact:Exact names:Names services:Services; do
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
