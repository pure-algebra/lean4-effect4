#!/usr/bin/env bash
# Detector-reaction suite for FIBER-PG-REPRESENTATIVE assurance.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
gate="$repo_root/scripts/check-fiber-assurance.sh"
generator="$repo_root/scripts/generate-fiber-assurance.sh"
projection="$repo_root/generated/fiber-assurance.tsv"
fixture_root="$repo_root/test/fixtures/fiber-assurance"

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-fiber-assurance-reaction.XXXXXX")"

cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-fiber-assurance-reaction.*) rm -rf -- "$tmp_root" ;;
    *)
      printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2
      cleanup_rc=1
      ;;
  esac
  exit "$cleanup_rc"
}
trap cleanup EXIT

[[ -x "$gate" ]] || { printf 'FAIL gate is not executable: %s\n' "$gate" >&2; exit 1; }
[[ -x "$generator" ]] || { printf 'FAIL generator is not executable: %s\n' "$generator" >&2; exit 1; }
[[ -f "$projection" && ! -L "$projection" ]] || {
  printf 'FAIL fixed generated Fiber projection is absent, not regular, or a symlink\n' >&2
  exit 1
}

lake_bin="$(command -v lake || true)"
[[ -n "$lake_bin" ]] || { printf 'FAIL lake is unavailable\n' >&2; exit 1; }

expect_lean_reject() {
  local label="$1"
  local fixture="$2"
  local signal="$3"
  local log="$tmp_root/$label.log"
  if (
      cd -- "$repo_root"
      unset LEAN_PATH LEAN_SRC_PATH
      "$lake_bin" env lean "$fixture"
    ) >"$log" 2>&1; then
    printf 'FAIL Fiber assurance checker accepted mutant: %s\n' "$label" >&2
    exit 1
  fi
  grep -Fq 'fiber assurance mismatch' "$log" || {
    printf 'FAIL mutant did not reach the Fiber assurance checker: %s\n' "$label" >&2
    cat "$log" >&2
    exit 1
  }
  grep -Fq "$signal" "$log" || {
    printf 'FAIL mutant lacked expected detector signal (%s): %s\n' "$signal" "$label" >&2
    cat "$log" >&2
    exit 1
  }
  if grep -Eq 'unknown (constant|identifier)|declaration uses .sorry|unexpected token' "$log"; then
    printf 'FAIL mutant was rejected by an unrelated elaboration failure: %s\n' "$label" >&2
    cat "$log" >&2
    exit 1
  fi
  printf 'PASS rejected Fiber assurance mutant: %s\n' "$label"
}

expect_lean_reject extra-public-declaration \
  "$fixture_root/ExtraDeclaration.lean" 'owned declaration census'
expect_lean_reject missing-public-declaration \
  "$fixture_root/MissingDeclaration.lean" 'missing declaration'
expect_lean_reject duplicate-public-declaration \
  "$fixture_root/DuplicateDeclaration.lean" 'duplicate owned declaration census'
expect_lean_reject declaration-owner-drift \
  "$fixture_root/OwnerDrift.lean" 'owner drift'

sed 's/FIBER-PG-REPRESENTATIVE\/IDENTITY/FIBER-PG-REPRESENTATIVE\/IDENTITY-STALE/' \
  "$projection" >"$tmp_root/stale.tsv"
if "$gate" --dry-run "$tmp_root/stale.tsv" >"$tmp_root/stale.log" 2>&1; then
  printf 'FAIL Fiber assurance gate accepted stale generated output\n' >&2
  exit 1
fi
grep -Fq 'stale generated Fiber assurance projection' "$tmp_root/stale.log" || {
  printf 'FAIL stale-output mutant lacked the drift detector signal\n' >&2
  cat "$tmp_root/stale.log" >&2
  exit 1
}
printf 'PASS rejected Fiber assurance mutant: stale-generated-output\n'

sed 's/`required-open`/`required-closed`/g' \
  "$repo_root/docs/FIBER-DAG.md" >"$tmp_root/manual-closure.md"
if cmp -s -- "$repo_root/docs/FIBER-DAG.md" "$tmp_root/manual-closure.md"; then
  printf 'FAIL manual-closure fixture did not mutate the authored Fiber graph\n' >&2
  exit 1
fi
if "$generator" --dry-run-dag "$tmp_root/manual-closure.md" \
    >"$tmp_root/manual-closure.tsv" 2>"$tmp_root/manual-closure.log"; then
  printf 'FAIL Fiber assurance generator accepted a manual closure override\n' >&2
  exit 1
fi
grep -Fq 'manual required-closed override' "$tmp_root/manual-closure.log" || {
  printf 'FAIL manual-closure mutant lacked the circularity detector signal\n' >&2
  cat "$tmp_root/manual-closure.log" >&2
  exit 1
}
printf 'PASS rejected Fiber assurance mutant: manual-closure-override\n'

# Supervision shape control and extra-field mutant exercise the existing audit
# boundary. The frozen production packet is never edited for a detector test.
cat >"$tmp_root/supervision-shape-control.lean" <<'SHAPE_CONTROL'
import Effect4Test.Concurrency.FiberAssurance
namespace Effect4Test.SupervisionShapeProbe
structure Options where
  startImmediately : Bool
  daemon : Bool
  maskMode : Nat
#effect4_check_supervision_shape Effect4Test.SupervisionShapeProbe.Options
  [Effect4Test.SupervisionShapeProbe.Options.mk] [startImmediately, daemon, maskMode]
end Effect4Test.SupervisionShapeProbe
SHAPE_CONTROL
(
  cd -- "$repo_root"
  unset LEAN_PATH LEAN_SRC_PATH
  "$lake_bin" env lean "$tmp_root/supervision-shape-control.lean"
) >"$tmp_root/supervision-shape-control.log" 2>&1 || {
  cat "$tmp_root/supervision-shape-control.log" >&2
  exit 1
}
sed '/  maskMode : Nat/a\
  unexpected : Nat
' "$tmp_root/supervision-shape-control.lean" >"$tmp_root/supervision-extra-field.lean"
expect_lean_reject supervision-extra-field \
  "$tmp_root/supervision-extra-field.lean" 'supervision structure field shape'

sed 's/`required-open`/`required-closed`/g' \
  "$repo_root/docs/SUPERVISION-DAG.md" >"$tmp_root/supervision-manual-closure.md"
if "$generator" --dry-run-supervision-dag "$tmp_root/supervision-manual-closure.md" \
    >"$tmp_root/supervision-manual-closure.tsv" 2>"$tmp_root/supervision-manual-closure.log"; then
  printf 'FAIL Supervision generator accepted a manual source-boundary closure\n' >&2
  exit 1
fi
grep -Fq 'manual required-closed override' "$tmp_root/supervision-manual-closure.log" || {
  printf 'FAIL Supervision manual-closure mutant lacked the boundary detector signal\n' >&2
  cat "$tmp_root/supervision-manual-closure.log" >&2
  exit 1
}
printf 'PASS rejected Supervision assurance mutant: manual-source-boundary-closure\n'

# The breaker's named type allocations and exact edge vocabulary are separate
# from count checks. Probe the two false acceptance paths found in review.
(
  cd -- "$repo_root"
  unset LEAN_PATH LEAN_SRC_PATH
  "$lake_bin" env lean Effect4Test/Concurrency/FiberAssurance.lean
) >"$tmp_root/supervision-driver.log" 2>&1
sed -n 's/^E4SUP\t//p' "$tmp_root/supervision-driver.log" >"$tmp_root/supervision-evidence.tsv"
check_supervision_candidate() {
  python3 "$repo_root/scripts/check-supervision-evidence.py" "$1" \
    "$repo_root/Effect4Test/Concurrency/FiberSupervisionContract.lean" \
    "$repo_root/Effect4Test/Concurrency/FiberSupervisionAxiomReport.lean" \
    "$repo_root/docs/SUPERVISION-DAG.md"
}
check_supervision_candidate "$tmp_root/supervision-evidence.tsv"
python3 - "$tmp_root/supervision-evidence.tsv" "$tmp_root" <<'SCHEMA_MUTANTS'
from pathlib import Path
import sys
rows = [line.split('\t') for line in Path(sys.argv[1]).read_text().splitlines()]
for kind, target, replacement, index, filename in [
    ('type', 'SUP-TYPE-WaitStep', 'Effect4.Supervision.waitStep_iff', 2, 'type-substitution.tsv'),
    ('graph-edge', 'SUPERVISION-PG-RC112/IDENTITY', 'SUPERVISION-PG-RC112/UNKNOWN-EDGE', 1, 'unknown-edge.tsv'),
]:
    candidate = [row.copy() for row in rows]
    matches = [row for row in candidate if row[0] == kind and row[1] == target]
    assert len(matches) == 1
    matches[0][index] = replacement
    Path(sys.argv[2], filename).write_text(''.join('\t'.join(row) + '\n' for row in candidate))
SCHEMA_MUTANTS
for label in type-substitution unknown-edge; do
  if check_supervision_candidate "$tmp_root/$label.tsv" >"$tmp_root/$label.log" 2>&1; then
    printf 'FAIL Supervision evidence schema accepted %s\n' "$label" >&2
    exit 1
  fi
  if [[ "$label" == type-substitution ]]; then
    signal='type receipts differ from frozen dispositions and routes'
  else
    signal='graph edge identifiers differ from the frozen DAG'
  fi
  grep -Fq "$signal" "$tmp_root/$label.log" || {
    cat "$tmp_root/$label.log" >&2
    exit 1
  }
  printf 'PASS rejected Supervision assurance mutant: %s\n' "$label"
done

"$gate"

printf 'PASS Fiber assurance gate reacts to 6/6 extra/missing/duplicate/owner/stale/manual-closure defects\n'
printf 'PASS all 7 required FIBER-PG-REPRESENTATIVE edges are closed from evidence\n'
printf 'PASS Supervision assurance reacts to 4/4 field/closure/type/edge defects; unmodified shape control passes\n'
