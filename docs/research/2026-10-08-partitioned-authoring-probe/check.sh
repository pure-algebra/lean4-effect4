#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
probe_dir=docs/research/2026-10-08-partitioned-authoring-probe
export LEAN_NUM_THREADS=3
lake build Effect4.Author Effect4.Laws.Author ProofGraph.Audit ProofGraph.Axioms | tee "$probe_dir/build.log"
lake env lean -DwarningAsError=true -o "$probe_dir/Model.olean" "$probe_dir/Model.lean" 2>&1 | tee "$probe_dir/model.log"
LEAN_PATH=. lake env lean -DwarningAsError=true -o "$probe_dir/Probe.olean" "$probe_dir/Probe.lean" 2>&1 | tee "$probe_dir/check.log"
LEAN_PATH=. lake env lean -DwarningAsError=true "$probe_dir/Trust.lean" 2>&1 | tee "$probe_dir/trust.log"
