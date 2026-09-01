#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
contract_file="Effect4Test/Concurrency/RaceRepresentativeContract.lean"
counterexample_file="Effect4Test/Counterexamples/Concurrency/RaceRepresentative.lean"
contract_doc="test/contracts/race-representative.contract.md"
dag_doc="docs/RACE-DAG.md"
register_file="test/counterexamples/REGISTER.md"
attacks_file="test/counterexamples/concurrency/ATTACKS.md"
known_red_file="test/fixtures/trust-gate/known-red.txt"
test_root="Effect4Test.lean"
contract_log="$(mktemp)"
counterexample_log="$(mktemp)"
dependency_log="$(mktemp)"
trap 'rm -f "$contract_log" "$counterexample_log" "$dependency_log"' EXIT

cd "$repo_root"

if ! lake build Effect4.Concurrency.Fiber Effect4.Concurrency.Interrupt \
    Effect4.Concurrency.Scheduler Effect4.Concurrency.Race \
    >"$dependency_log" 2>&1; then
  echo "race representative production dependencies did not compile" >&2
  cat "$dependency_log" >&2
  exit 1
fi

if ! lake env lean "$counterexample_file" >"$counterexample_log" 2>&1; then
  echo "race representative counterexamples did not compile" >&2
  cat "$counterexample_log" >&2
  exit 1
fi

if grep -Eq '\b(sorry|admit|native_decide|Classical\.choice)\b' \
    "$counterexample_file" "$contract_file"; then
  echo "race representative packet contains a forbidden proof escape" >&2
  exit 1
fi

for suffix in 008 009 010 011; do
  id="E4-CONC-CE-${suffix}"
  if [[ "$(grep -c "$id" "$register_file")" -ne 1 ]]; then
    echo "race representative register must contain $id exactly once" >&2
    exit 1
  fi
  if [[ "$(grep -c "^## $id " "$attacks_file")" -ne 1 ]]; then
    echo "race representative attacks must contain $id exactly once" >&2
    exit 1
  fi
done

for witness in \
  erased_winner_choice_counterexample \
  first_completion_ne_first_success_counterexample \
  early_return_before_loser_cleanup_counterexample \
  masked_loser_is_live_frontier_counterexample; do
  if [[ "$(grep -c "^theorem $witness" "$counterexample_file")" -ne 1 ]]; then
    echo "race representative witness must define $witness exactly once" >&2
    exit 1
  fi
  receipt="'Effect4Test.Counterexamples.Concurrency.RaceRepresentative.${witness}' does not depend on any axioms"
  if [[ "$(grep -Fc "$receipt" "$counterexample_log")" -ne 1 ]]; then
    echo "race representative witness $witness is missing its axiom-free receipt" >&2
    cat "$counterexample_log" >&2
    exit 1
  fi
done

if [[ "$(grep -c '^#effect4_check_race_forbidden_declarations$' \
    "$contract_file")" -ne 1 ]] ||
    [[ "$(grep -c '^#effect4_check_race_declaration_shapes$' \
      "$contract_file")" -ne 1 ]]; then
  echo "race representative contract must execute both environment gates exactly once" >&2
  exit 1
fi

if [[ "$(grep -c '^import Effect4Test\.Counterexamples\.Concurrency\.RaceRepresentative$' \
    "$test_root")" -ne 1 ]]; then
  echo "race representative counterexamples are not closed through Effect4Test.lean" >&2
  exit 1
fi

if [[ "$(grep -c '^Effect4Test\.Concurrency\.RaceRepresentativeContract$' \
    "$known_red_file")" -ne 1 ]]; then
  echo "race representative known-red routing must occur exactly once" >&2
  exit 1
fi

if lake env lean -DmaxErrors=10000 "$contract_file" >"$contract_log" 2>&1; then
  echo "race representative contract unexpectedly passed; breaker is no longer red" >&2
  exit 1
fi

for sentinel in \
  'race declaration shape mismatch for Effect4.RaceSpec: declaration is absent' \
  'Unknown identifier `RaceSpec`' \
  'Unknown identifier `RaceState`' \
  'Unknown identifier `RaceDecision`' \
  'Unknown identifier `RaceRefusal`' \
  'Unknown identifier `raceStepEval`' \
  'Unknown identifier `RaceRuns`' \
  'Unknown identifier `RaceState.settled_iff`' \
  'Unknown identifier `RaceDecision.beforeSelection_iff`' \
  'Unknown identifier `RaceStepResult.fromScheduler_advanced`'; do
  if ! grep -Fq "$sentinel" "$contract_log"; then
    echo "race representative red was not caused by missing $sentinel" >&2
    cat "$contract_log" >&2
    exit 1
  fi
done

if grep -Fq 'race forbidden duplicate declaration is present' "$contract_log" ||
    grep -Fq 'race forbidden first-success declaration is present' "$contract_log"; then
  echo "race representative environment gate found a forbidden declaration" >&2
  cat "$contract_log" >&2
  exit 1
fi

if grep -Eq 'unexpected token|unknown namespace|invalid import|declaration uses \.sorry|failed to synthesize|type mismatch|application type mismatch' \
    "$contract_log"; then
  echo "race representative contract failed for an unrelated reason" >&2
  cat "$contract_log" >&2
  exit 1
fi

echo "race representative production dependencies: green"
echo "race representative counterexamples: green (4/4)"
echo "race representative implementation contract: clean red"
