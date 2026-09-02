#!/usr/bin/env bash
# Deterministic joins for FIBER-PG-REPRESENTATIVE and SUPERVISION-PG-RC112.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
generator_rel="scripts/generate-fiber-assurance.sh"
interrupt_rel="Effect4/Concurrency/Interrupt.lean"
fiber_rel="Effect4/Concurrency/Fiber.lean"
scheduler_rel="Effect4/Concurrency/Scheduler.lean"
contract_rel="test/contracts/fiber-representative.contract.md"
lean_contract_rel="Effect4Test/Concurrency/FiberRepresentativeContract.lean"
assurance_rel="Effect4Test/Concurrency/FiberAssurance.lean"
axiom_report_rel="Effect4Test/Concurrency/FiberAxiomReport.lean"
counterexample_rel="Effect4Test/Counterexamples/Concurrency/FiberRepresentative.lean"
dag_rel="docs/FIBER-DAG.md"
register_rel="test/counterexamples/REGISTER.md"
attacks_rel="test/counterexamples/concurrency/ATTACKS.md"

expected_contract_sha="09909af0e729ac49c3936c19c3dbfe5aba381c653b03c580668821b4b5f9b1af"
expected_battery_sha="9926fe9d7bc4a2969217cf9ac32abb6f160700fa657256a7d5f5e3503c37bc1f"
expected_dag_sha="75959e24cc35eb69fe8ebbc08df81bcc998d71d6d2949ba6fa472d0c29e7c14e"

contract_source="$repo_root/$contract_rel"
dag_source="$repo_root/$dag_rel"
supervision_rel="Effect4/Concurrency/Supervision.lean"
supervision_contract_rel="test/contracts/fiber-supervision.contract.md"
supervision_battery_rel="Effect4Test/Concurrency/FiberSupervisionContract.lean"
supervision_axioms_rel="Effect4Test/Concurrency/FiberSupervisionAxiomReport.lean"
supervision_counterexample_rel="Effect4Test/Counterexamples/Concurrency/FiberSupervision.lean"
supervision_dag_rel="docs/SUPERVISION-DAG.md"
supervision_dag_source="$repo_root/$supervision_dag_rel"
generation_mode="production"
if [[ $# -gt 0 ]]; then
  if [[ $# -eq 2 && "$1" == "--dry-run-contract" ]]; then
    generation_mode="dry-run-contract"
    contract_source="$2"
  elif [[ $# -eq 2 && "$1" == "--dry-run-dag" ]]; then
    generation_mode="dry-run-dag"
    dag_source="$2"
  elif [[ $# -eq 2 && "$1" == "--dry-run-supervision-dag" ]]; then
    generation_mode="dry-run-supervision-dag"
    supervision_dag_source="$2"
  else
    printf 'usage: generate-fiber-assurance.sh [--dry-run-contract <contract.md> | --dry-run-dag <FIBER-DAG.md> | --dry-run-supervision-dag <SUPERVISION-DAG.md>]\n' >&2
    exit 2
  fi
fi

for override_name in \
    EFFECT4_FIBER_SOURCE \
    EFFECT4_FIBER_CONTRACT \
    EFFECT4_FIBER_BATTERY \
    EFFECT4_FIBER_ASSURANCE_DRIVER \
    EFFECT4_FIBER_AXIOM_REPORT \
    EFFECT4_SUPERVISION_SOURCE \
    EFFECT4_SUPERVISION_DAG \
    EFFECT4_SUPERVISION_BATTERY; do
  if [[ -n "${!override_name-}" ]]; then
    printf 'FAIL Fiber assurance generator rejects source override variable %s\n' \
      "$override_name" >&2
    exit 2
  fi
done

for required in \
    "$repo_root/$generator_rel" \
    "$repo_root/$interrupt_rel" \
    "$repo_root/$fiber_rel" \
    "$repo_root/$scheduler_rel" \
    "$repo_root/$lean_contract_rel" \
    "$repo_root/$assurance_rel" \
    "$repo_root/$axiom_report_rel" \
    "$repo_root/$counterexample_rel" \
    "$dag_source" \
    "$repo_root/$register_rel" \
    "$repo_root/$attacks_rel" \
    "$contract_source" \
    "$repo_root/$supervision_rel" \
    "$repo_root/$supervision_contract_rel" \
    "$repo_root/$supervision_battery_rel" \
    "$repo_root/$supervision_axioms_rel" \
    "$repo_root/$supervision_counterexample_rel" \
    "$supervision_dag_source" \
    "$repo_root/PORT-MANIFEST.md" \
    "$repo_root/scripts/check-supervision-evidence.py"; do
  [[ -f "$required" && ! -L "$required" ]] || {
    printf 'FAIL required Fiber assurance input is absent, not regular, or a symlink: %s\n' \
      "$required" >&2
    exit 1
  }
done

lake_bin="$(command -v lake || true)"
[[ -n "$lake_bin" ]] || { printf 'FAIL lake is unavailable\n' >&2; exit 1; }

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    printf 'FAIL neither sha256sum nor shasum is available\n' >&2
    return 1
  fi
}

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-fiber-assurance.XXXXXX")"

cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-fiber-assurance.*) rm -rf -- "$tmp_root" ;;
    *)
      printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2
      cleanup_rc=1
      ;;
  esac
  exit "$cleanup_rc"
}
trap cleanup EXIT

require_text() {
  local file="$1"
  local required_text="$2"
  grep -Fq -- "$required_text" "$file" || {
    printf 'FAIL required Fiber assurance text is absent from %s: %s\n' \
      "$file" "$required_text" >&2
    exit 1
  }
}

# The controller join cannot turn the required source interpretation into a
# completed or inapplicable edge. Frozen hashes also preserve the red packet.
if grep -Fq -- '`required-closed`' "$supervision_dag_source"; then
  printf 'FAIL Supervision authored graph carries a manual required-closed override\n' >&2
  exit 1
fi
while IFS=$'\t' read -r input_rel expected_sha; do
  input_file="$repo_root/$input_rel"
  [[ "$input_rel" != "$supervision_dag_rel" ]] || input_file="$supervision_dag_source"
  actual_sha="$(sha256_file "$input_file")"
  [[ "$actual_sha" == "$expected_sha" ]] || {
    printf 'FAIL frozen Supervision packet hash drifted: %s\n' "$input_rel" >&2
    exit 1
  }
done <<'SUPERVISION_FROZEN'
test/contracts/fiber-supervision.contract.md	abad19a1e90110dcd7dbfc2d5597865890b525c3475cea6bd18a256b6d48b9c6
docs/SUPERVISION-DAG.md	acee8b741e2119b8830a09af969b033cd644ea68514a7d36b30ca525a859c30d
Effect4Test/Concurrency/FiberSupervisionContract.lean	a42de6350616a0fbbe94bfcde471cc607e0c5a84fe601704a4911cc1eff61651
Effect4Test/Concurrency/FiberSupervisionAxiomReport.lean	9bdfe6d385b65ae0a1d2487c6a7b87e75b0df7eecf58feacb75cffa018047c2c
Effect4Test/Counterexamples/Concurrency/FiberSupervision.lean	52980b4e901f52f19528e2dbf71853c7ac0fa05549680306a1ef418d4a2428b7
SUPERVISION_FROZEN

python3 - "$supervision_dag_source" "$repo_root/PORT-MANIFEST.md" <<'SUPERVISION_MIRROR'
from pathlib import Path
import sys

def rows(text, heading, end):
    section = text.split(heading, 1)[1].split(end, 1)[0]
    return [[cell.strip() for cell in line.strip('|').split('|')]
            for line in section.splitlines() if line.startswith('| `')]

dag = rows(Path(sys.argv[1]).read_text(), '## Complete type and judgment disposition',
           '`Fiber.toFiberState_eq`')
manifest = rows(Path(sys.argv[2]).read_text(), '## Fork and supervision declaration dispositions',
                '## Retained TypeScript target fragment')
expected = []
for name, disposition, relation, route in dag:
    expected.append(['`Effect4.Supervision.' + name.strip('`') + '`',
                     '`Concurrency/Supervision.lean`', disposition, relation, route])
if len(expected) != 27 or manifest != expected:
    raise SystemExit('FAIL Supervision manifest dispositions differ from the frozen DAG')
SUPERVISION_MIRROR

for suffix in 012 013 014 015 016 017 018 019 020 021 022 023 024 025 026; do
  id="E4-CONC-CE-$suffix"
  count="$(grep -Fc -- "| \`$id\` |" "$repo_root/$register_rel" || true)"
  [[ "$count" == 1 ]] || { printf 'FAIL Supervision counterexample row %s count=%s\n' "$id" "$count" >&2; exit 1; }
  require_text "$repo_root/$attacks_rel" "## $id — "
  require_text "$repo_root/$supervision_counterexample_rel" "$id"
done

# Closure is derived by this join. The frozen breaker contract cannot close
# its own graph.
if grep -Fq -- '`required-closed`' "$contract_source" ||
    grep -Fq -- '`required-closed`' "$dag_source"; then
  printf 'FAIL Fiber authored graph carries a manual required-closed override\n' >&2
  exit 1
fi

actual_contract_sha="$(sha256_file "$contract_source")"
[[ "$actual_contract_sha" == "$expected_contract_sha" ]] || {
  printf 'FAIL frozen Fiber contract hash drifted: expected %s, found %s\n' \
    "$expected_contract_sha" "$actual_contract_sha" >&2
  exit 1
}
actual_battery_sha="$(sha256_file "$repo_root/$lean_contract_rel")"
[[ "$actual_battery_sha" == "$expected_battery_sha" ]] || {
  printf 'FAIL frozen Fiber battery hash drifted: expected %s, found %s\n' \
    "$expected_battery_sha" "$actual_battery_sha" >&2
  exit 1
}
actual_dag_sha="$(sha256_file "$dag_source")"
[[ "$actual_dag_sha" == "$expected_dag_sha" ]] || {
  printf 'FAIL frozen Fiber DAG hash drifted: expected %s, found %s\n' \
    "$expected_dag_sha" "$actual_dag_sha" >&2
  exit 1
}

require_text "$contract_source" 'Status: FROZEN / RED, breaker-authored 2026-08-31'
require_text "$contract_source" '`FIBER-PG-REPRESENTATIVE`'
require_text "$contract_source" 'There is no untaped determinism'
require_text "$contract_source" '`ReplayResult.frontier machine`'
require_text "$contract_source" 'does not mint a duplicate Frontier'
require_text "$contract_source" 'does not mint a second machine carrier'

required_edges=(identity construction semantics laws counterexamples trust coverage)
not_applicable_edges=(representation bridges targets)
for edge in "${required_edges[@]}"; do
  matches="$tmp_root/edge-$edge.matches"
  needle='| '"$edge"' | `required-open` |'
  grep -F -- "$needle" "$dag_source" >"$matches" || true
  count="$(wc -l <"$matches" | tr -d ' ')"
  [[ "$count" == 1 ]] || {
    printf 'FAIL Fiber graph edge %s has %s required-open rows; expected once\n' \
      "$edge" "$count" >&2
    exit 1
  }
done
for edge in "${not_applicable_edges[@]}"; do
  matches="$tmp_root/edge-$edge.matches"
  needle='| '"$edge"' | `not-applicable` |'
  grep -F -- "$needle" "$dag_source" >"$matches" || true
  count="$(wc -l <"$matches" | tr -d ' ')"
  [[ "$count" == 1 ]] || {
    printf 'FAIL Fiber graph edge %s has %s not-applicable rows; expected once\n' \
      "$edge" "$count" >&2
    exit 1
  }
done

counterexample_rows="$tmp_root/counterexamples.rows"
: >"$counterexample_rows"
for suffix in 001 002 003 004 005 006 007; do
  counterexample_id="E4-CONC-CE-$suffix"
  matches="$tmp_root/$counterexample_id.matches"
  needle='| `'$counterexample_id'` |'
  grep -F -- "$needle" "$repo_root/$register_rel" >"$matches" || true
  count="$(wc -l <"$matches" | tr -d ' ')"
  [[ "$count" == 1 ]] || {
    printf 'FAIL Fiber counterexample registration %s occurs %s times; expected once\n' \
      "$counterexample_id" "$count" >&2
    exit 1
  }
  require_text "$matches" '| SEEDED |'
  heading_count="$(grep -Ec -- "^## $counterexample_id — " "$repo_root/$attacks_rel" || true)"
  [[ "$heading_count" == 1 ]] || {
    printf 'FAIL Fiber attack heading %s occurs %s times; expected once\n' \
      "$counterexample_id" "$heading_count" >&2
    exit 1
  }
  witness_count="$(grep -Fc -- "$counterexample_id" "$repo_root/$counterexample_rel" || true)"
  [[ "$witness_count" -ge 1 ]] || {
    printf 'FAIL Fiber executable witness does not cite %s\n' "$counterexample_id" >&2
    exit 1
  }
  cat "$matches" >>"$counterexample_rows"
done

(
  cd -- "$repo_root"
  unset LEAN_PATH LEAN_SRC_PATH
  "$lake_bin" build Effect4Test.Concurrency.FiberAssurance >"$tmp_root/build.log" 2>&1
  "$lake_bin" env lean "$lean_contract_rel" >"$tmp_root/contract.log" 2>&1
  "$lake_bin" env lean "$counterexample_rel" >"$tmp_root/counterexamples.log" 2>&1
  "$lake_bin" env lean "$axiom_report_rel" >"$tmp_root/axioms.log" 2>&1
  "$lake_bin" env lean -DmaxErrors=10000 "$supervision_battery_rel" >"$tmp_root/supervision-contract.log" 2>&1
  "$lake_bin" env lean "$supervision_counterexample_rel" >"$tmp_root/supervision-counterexamples.log" 2>&1
  "$lake_bin" env lean "$supervision_axioms_rel" >"$tmp_root/supervision-axioms.log" 2>&1
  "$lake_bin" env lean "$assurance_rel" >"$tmp_root/driver.log" 2>&1
)

grep $'^E4FIBER\t' "$tmp_root/driver.log" >"$tmp_root/evidence.rows" || {
  printf 'FAIL Fiber assurance driver emitted no evidence rows\n' >&2
  cat "$tmp_root/driver.log" >&2
  exit 1
}
sed 's/^E4FIBER\t//' "$tmp_root/evidence.rows" >"$tmp_root/evidence.tsv"

evidence_count() {
  awk -F '\t' -v kind="$1" '$1 == kind { count++ } END { print count + 0 }' \
    "$tmp_root/evidence.tsv"
}

owned_count="$(evidence_count owned-declaration)"
interrupt_owned_count="$(awk -F '\t' '$1 == "owned-declaration" && $3 == "Effect4.Concurrency.Interrupt" {count++} END {print count+0}' "$tmp_root/evidence.tsv")"
fiber_owned_count="$(awk -F '\t' '$1 == "owned-declaration" && $3 == "Effect4.Concurrency.Fiber" {count++} END {print count+0}' "$tmp_root/evidence.tsv")"
scheduler_owned_count="$(awk -F '\t' '$1 == "owned-declaration" && $3 == "Effect4.Concurrency.Scheduler" {count++} END {print count+0}' "$tmp_root/evidence.tsv")"
api_count="$(evidence_count api)"
theorem_count="$(evidence_count theorem)"
axiom_count="$(evidence_count axiom)"
type_count="$(evidence_count type)"
leaf_count="$(evidence_count leaf-receipt)"
absent_count="$(evidence_count absent)"
edge_count="$(evidence_count graph-edge)"

[[ "$owned_count" == 504 && "$interrupt_owned_count" == 62 && \
   "$fiber_owned_count" == 79 && "$scheduler_owned_count" == 363 ]] || {
  printf 'FAIL Fiber owned census is total=%s interrupt=%s fiber=%s scheduler=%s; expected 504/62/79/363\n' \
    "$owned_count" "$interrupt_owned_count" "$fiber_owned_count" "$scheduler_owned_count" >&2
  exit 1
}
[[ "$api_count" == 185 ]] || {
  printf 'FAIL Fiber authored API emitted %s rows; expected 185\n' "$api_count" >&2
  exit 1
}
[[ "$theorem_count" == 92 && "$axiom_count" == 92 ]] || {
  printf 'FAIL Fiber theorem/axiom receipt counts are %s/%s; expected 92/92\n' \
    "$theorem_count" "$axiom_count" >&2
  exit 1
}
[[ "$type_count" == 16 && "$leaf_count" == 14 ]] || {
  printf 'FAIL Fiber type/leaf receipt counts are %s/%s; expected 16/14\n' \
    "$type_count" "$leaf_count" >&2
  exit 1
}
[[ "$absent_count" == 12 ]] || {
  printf 'FAIL Fiber duplicate-prevention receipts emitted %s rows; expected 12\n' \
    "$absent_count" >&2
  exit 1
}
[[ "$edge_count" == 10 ]] || {
  printf 'FAIL FIBER-PG-REPRESENTATIVE emitted %s edges; expected 10\n' "$edge_count" >&2
  exit 1
}

for edge in "${required_edges[@]}"; do
  edge_upper="$(printf '%s' "$edge" | tr '[:lower:]' '[:upper:]')"
  edge_id="FIBER-PG-REPRESENTATIVE/$edge_upper"
  count="$(awk -F '\t' -v edge_id="$edge_id" \
    '$1 == "graph-edge" && $2 == edge_id && $4 == "required" { count++ } END { print count + 0 }' \
    "$tmp_root/evidence.tsv")"
  [[ "$count" == 1 ]] || {
    printf 'FAIL required Fiber graph edge %s emitted %s matching rows; expected once\n' \
      "$edge_id" "$count" >&2
    exit 1
  }
done
for edge in "${not_applicable_edges[@]}"; do
  edge_upper="$(printf '%s' "$edge" | tr '[:lower:]' '[:upper:]')"
  edge_id="FIBER-PG-REPRESENTATIVE/$edge_upper"
  count="$(awk -F '\t' -v edge_id="$edge_id" \
    '$1 == "graph-edge" && $2 == edge_id && $4 == "not-applicable" { count++ } END { print count + 0 }' \
    "$tmp_root/evidence.tsv")"
  [[ "$count" == 1 ]] || {
    printf 'FAIL not-applicable Fiber graph edge %s emitted %s matching rows; expected once\n' \
      "$edge_id" "$count" >&2
    exit 1
  }
done

awk '/^#print axioms / { print $3 }' "$repo_root/$axiom_report_rel" \
  >"$tmp_root/axiom-report.names"
awk -F '\t' '$1 == "theorem" { print $2 }' "$tmp_root/evidence.tsv" \
  >"$tmp_root/theorem.names"
if ! cmp -s -- "$tmp_root/axiom-report.names" "$tmp_root/theorem.names"; then
  printf 'FAIL Fiber axiom report names do not exactly match all authored theorem receipts\n' >&2
  diff -u -- "$tmp_root/theorem.names" "$tmp_root/axiom-report.names" >&2 || true
  exit 1
fi

invalid_axiom_rows="$(awk -F '\t' \
  '$1 == "axiom" && $3 != "none" && $3 != "propext" && \
   $3 != "Quot.sound" && $3 != "propext,Quot.sound" { count++ } \
   END { print count + 0 }' "$tmp_root/evidence.tsv")"
[[ "$invalid_axiom_rows" == 0 ]] || {
  printf 'FAIL Fiber assurance emitted %s noncanonical axiom rows\n' \
    "$invalid_axiom_rows" >&2
  exit 1
}

for leaf in \
    FIBER-LEAF-ID FIBER-LEAF-STATUS FIBER-LEAF-STATE \
    FIBER-LEAF-INTERRUPT-MASK FIBER-LEAF-CLEANUP-STATE FIBER-LEAF-BOUNDARY \
    FIBER-LEAF-REFUSAL FIBER-LEAF-DECISION FIBER-LEAF-TAPE FIBER-LEAF-EVENT \
    FIBER-LEAF-TRACE FIBER-LEAF-MACHINE FIBER-LEAF-STEP-RESULT \
    FIBER-LEAF-REPLAY-RESULT; do
  count="$(awk -F '\t' -v leaf="$leaf" '$1 == "leaf-receipt" && $2 == leaf {count++} END {print count+0}' "$tmp_root/evidence.tsv")"
  [[ "$count" == 1 ]] || {
    printf 'FAIL Fiber leaf receipt %s occurs %s times; expected once\n' "$leaf" "$count" >&2
    exit 1
  }
done

grep $'^E4SUP\t' "$tmp_root/driver.log" >"$tmp_root/supervision.rows" || {
  printf 'FAIL Supervision assurance driver emitted no evidence rows\n' >&2
  exit 1
}
sed 's/^E4SUP\t//' "$tmp_root/supervision.rows" >"$tmp_root/supervision.tsv"
python3 "$repo_root/scripts/check-supervision-evidence.py" \
  "$tmp_root/supervision.tsv" "$repo_root/$supervision_battery_rel" \
  "$repo_root/$supervision_axioms_rel" "$supervision_dag_source"

printf 'format\teffect4-fiber-assurance-v1\n'
printf 'generator\t%s\tsha256=%s\n' "$generator_rel" "$(sha256_file "$repo_root/$generator_rel")"
printf 'regenerate\t./scripts/generate-fiber-assurance.sh > generated/fiber-assurance.tsv\n'
for input_rel in \
    "$interrupt_rel" "$fiber_rel" "$scheduler_rel" "$contract_rel" \
    "$lean_contract_rel" "$assurance_rel" "$axiom_report_rel" \
    "$counterexample_rel" "$dag_rel" "$register_rel" "$attacks_rel"; do
  input_file="$repo_root/$input_rel"
  if [[ "$input_rel" == "$contract_rel" ]]; then
    input_file="$contract_source"
  elif [[ "$input_rel" == "$dag_rel" ]]; then
    input_file="$dag_source"
  fi
  printf 'input\t%s\tsha256=%s\n' "$input_rel" "$(sha256_file "$input_file")"
done
printf 'contract\tFIBER-EV-REPRESENTATIVE-CONTRACT\t%s\trequired-closed\n' "$contract_rel"
printf 'battery\tFIBER-REPRESENTATIVE-FROZEN-BATTERY\t%s\tsha256=%s\trequired-closed\n' \
  "$lean_contract_rel" "$actual_battery_sha"
printf 'graph-owner\tFIBER-PG-REPRESENTATIVE\tEffect4.Step+Effect4.Runs\tgraph\trequired-closed\n'
for suffix in 001 002 003 004 005 006 007; do
  printf 'counterexample\tE4-CONC-CE-%s\tSEEDED\t%s\t%s\trequired-closed\n' \
    "$suffix" "$register_rel" "$counterexample_rel"
done

awk -F '\t' 'BEGIN { OFS="\t" }
  $1 == "graph-edge" && $4 == "required" {
    print $1, $2, $3, "required-closed"; next
  }
  { print }
' "$tmp_root/evidence.tsv"

# Supervision retains its open host route. Only six local edges close after
# the fixed packet, exact driver, counterexample, and axiom checks above.
for input_rel in \
    "$supervision_rel" "$supervision_contract_rel" "$supervision_battery_rel" \
    "$supervision_axioms_rel" "$supervision_counterexample_rel" "$supervision_dag_rel" \
    PORT-MANIFEST.md scripts/check-supervision-evidence.py \
    harness/fiber-supervision/host-pin.json \
    harness/fiber-supervision/runtime-check.ts scripts/check-fiber-supervision-host.sh; do
  printf 'input\t%s\tsha256=%s\n' "$input_rel" "$(sha256_file "$repo_root/$input_rel")"
done
printf 'contract\tSUPERVISION-FROZEN-CONTRACT\t%s\trequired-closed\n' "$supervision_contract_rel"
printf 'battery\tSUPERVISION-FROZEN-BATTERY\t%s\trequired-closed\n' "$supervision_battery_rel"
printf 'graph-owner\tSUPERVISION-PG-RC112\tEffect4.Supervision.WaitRuns+Effect4.Supervision.RaceRuns\tgraph\trequired-open\n'
for suffix in 012 013 014 015 016 017 018 019 020 021 022 023 024 025 026; do
  printf 'counterexample\tE4-CONC-CE-%s\tSEEDED\t%s\t%s\trequired-closed\n'     "$suffix" "$register_rel" "$supervision_counterexample_rel"
done
awk -F '\t' 'BEGIN { OFS="\t" }
  $1 == "graph-edge" && $4 == "required-local" {
    print $1, $2, $3, "required-closed"; next
  }
  { print }
' "$tmp_root/supervision.tsv"
