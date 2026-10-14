#!/bin/bash
set -eu
evidence_dir="$(cd "$(dirname "$0")" && pwd)"
check_dir="${1:?Supply an absolute scratch directory for the check outputs}"
mkdir -p "$check_dir"
lake build Effect4.Laws.Program.DenoteCtl Effect4.Laws.Program.BlockMeaning \
  Effect4.Laws.Api.SessionMeaningBlocks Effect4.Laws.Run.CallTree \
  Test.Dogfood.Scenario.Workers Test.Dogfood.Scenario.QueueWorkers \
  Test.Dogfood.Scenario.Timeout Test.Dogfood.Scenario.Atomic \
  Effect4.Laws.Program.FinalizerRun ProofGraph.Plan ProofGraph.AxiomAudit \
  > "$check_dir/build.log" 2>&1
lake env lean -DwarningAsError=true --root="$evidence_dir" \
  -o "$check_dir/MeaningsPrefixProbe.olean" "$evidence_dir/MeaningsPrefixProbe.lean" \
  > "$check_dir/probe.log" 2>&1
LEAN_PATH="$check_dir${LEAN_PATH:+:$LEAN_PATH}" \
  lake env lean -DwarningAsError=true "$evidence_dir/Audit.lean" \
  > "$check_dir/audit.log" 2>&1
lake env lean -DwarningAsError=true "$evidence_dir/Frontier.lean" \
  > "$check_dir/frontier.log" 2>&1
printf '%s\n' "Verified evidence in $check_dir"
