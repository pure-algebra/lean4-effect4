#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
counterexample_file="Effect4Test/Counterexamples/Concurrency/FiberRepresentative.lean"
contract_file="Effect4Test/Concurrency/FiberRepresentativeContract.lean"
sentinel_file="test/fixtures/fiber-representative/expected-red.txt"
contract_doc="test/contracts/fiber-representative.contract.md"
dag_doc="docs/FIBER-DAG.md"
attacks_file="test/counterexamples/concurrency/ATTACKS.md"
register_file="test/counterexamples/REGISTER.md"
counterexample_log="$(mktemp)"
contract_log="$(mktemp)"
trap 'rm -f "$counterexample_log" "$contract_log"' EXIT

cd "$repo_root"

if ! lake env lean "$counterexample_file" >"$counterexample_log" 2>&1; then
  echo "fiber representative counterexamples did not compile" >&2
  cat "$counterexample_log" >&2
  exit 1
fi

if grep -Eq '\b(sorry|admit|native_decide|Classical\.choice)\b' \
    "$counterexample_file" "$contract_file"; then
  echo "fiber representative packet contains a forbidden proof escape" >&2
  exit 1
fi

if grep -Eq '\b(FiberTerminal|joinBeforeDone|cleanupStarted)\b|Frontier\.tapeExhausted' \
    "$contract_file" "$contract_doc" "$dag_doc"; then
  echo "fiber representative packet reintroduced a foreign or retired carrier" >&2
  exit 1
fi

for suffix in 001 002 003 004 005 006; do
  id="E4-CONC-CE-${suffix}"
  if [[ "$(grep -c "$id" "$register_file")" -ne 1 ]]; then
    echo "fiber representative register must contain $id exactly once" >&2
    exit 1
  fi
  if [[ "$(grep -c "^## $id " "$attacks_file")" -ne 1 ]]; then
    echo "fiber representative attacks must contain $id exactly once" >&2
    exit 1
  fi
done

if lake env lean -DmaxErrors=10000 "$contract_file" >"$contract_log" 2>&1; then
  echo "fiber representative contract unexpectedly passed; breaker is no longer red" >&2
  exit 1
fi

while IFS= read -r sentinel; do
  if [[ -n "$sentinel" ]] && ! grep -Fq "$sentinel" "$contract_log"; then
    echo "fiber representative red was not caused by missing $sentinel" >&2
    cat "$contract_log" >&2
    exit 1
  fi
done < "$sentinel_file"

if grep -Eq 'unknown module|Unknown identifier|invalid import|unexpected token|declaration uses .sorry' \
    "$contract_log"; then
  echo "fiber representative contract failed for an unrelated reason" >&2
  cat "$contract_log" >&2
  exit 1
fi

echo "fiber representative counterexamples: green"
echo "fiber representative implementation contract: clean red"
