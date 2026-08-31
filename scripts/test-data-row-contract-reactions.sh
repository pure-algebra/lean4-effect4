#!/usr/bin/env bash
# Bounded red-phase reaction test for the frozen Data.Row contract. It proves
# the empty-stub diagnostic census is clean and that four forbidden public
# routes disturb their exact absence guards. It does not test the future
# implementation's semantic equations; those are the Lean battery's job.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
fixture_root="$repo_root/test/fixtures/data-row-contract"
tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-data-row-contract.XXXXXX")"

cleanup() {
  local cleanup_status=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-data-row-contract.*) rm -rf -- "$tmp_root" ;;
    *)
      printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2
      cleanup_status=1
      ;;
  esac
  exit "$cleanup_status"
}
trap cleanup EXIT

lake_bin="$(command -v lake || true)"
[[ -n "$lake_bin" ]] || { printf 'FAIL lake is unavailable\n' >&2; exit 1; }

for required in \
    "$repo_root/lakefile.toml" \
    "$repo_root/lake-manifest.json" \
    "$repo_root/lean-toolchain" \
    "$repo_root/Effect4/Data/Row.lean" \
    "$repo_root/Effect4Test/Data/RowContract.lean" \
    "$fixture_root/custom-row-order.lean.txt" \
    "$fixture_root/unchecked-of-list.lean.txt" \
    "$fixture_root/append-route.lean.txt" \
    "$fixture_root/denotation-claim.lean.txt"; do
  [[ -f "$required" && ! -L "$required" ]] || {
    printf 'FAIL required source is absent, not regular, or a symlink: %s\n' \
      "$required" >&2
    exit 1
  }
done

make_project() {
  local project="$1"
  mkdir -p "$project"
  cp "$repo_root/lakefile.toml" "$repo_root/lake-manifest.json" \
    "$repo_root/lean-toolchain" "$repo_root/Effect4.lean" \
    "$repo_root/Effect4Test.lean" "$project/"
  cp -R "$repo_root/Effect4" "$repo_root/Effect4Test" "$project/"
}

run_contract_red() {
  local project="$1"
  local log="$2"
  (
    cd -- "$project"
    unset LEAN_PATH LEAN_SRC_PATH
    "$lake_bin" build Effect4.Data.Row >/dev/null
    ! "$lake_bin" env lean -DmaxErrors=10000 --json \
      Effect4Test/Data/RowContract.lean >"$log" 2>&1
  )
}

baseline="$tmp_root/baseline"
baseline_log="$tmp_root/baseline.jsonl"
make_project "$baseline"
run_contract_red "$baseline" "$baseline_log"

error_count="$(grep -c '"severity":"error"' "$baseline_log" || true)"
unknown_count="$(grep -c \
  '"kind":"lean.unknownIdentifier._namedError"' "$baseline_log" || true)"
other_count="$(grep '"severity":"error"' "$baseline_log" \
  | grep -vc '"kind":"lean.unknownIdentifier._namedError"' || true)"
distinct_count="$(grep '"kind":"lean.unknownIdentifier._namedError"' \
  "$baseline_log" \
  | sed -n 's/.*"data":"Unknown identifier `\([^`]*\)`.*/\1/p' \
  | LC_ALL=C sort -u | wc -l | tr -d '[:space:]')"

if [[ "$error_count" != 118 || "$unknown_count" != 118 \
    || "$other_count" != 0 || "$distinct_count" != 34 ]]; then
  printf 'FAIL Data.Row clean-red census drifted: errors=%s unknown=%s other=%s distinct=%s\n' \
    "$error_count" "$unknown_count" "$other_count" "$distinct_count" >&2
  tail -80 "$baseline_log" >&2
  exit 1
fi
printf 'PASS Data.Row empty stub is clean-red: 118/118 unknown identifiers, 34 names\n'

expect_forbidden_route_rejected() {
  local label="$1"
  local fixture="$2"
  local signal="$3"
  local project="$tmp_root/$label"
  local log="$tmp_root/$label.jsonl"
  make_project "$project"
  sed -n '1,$p' "$fixture" >>"$project/Effect4/Data/Row.lean"
  run_contract_red "$project" "$log"

  if ! grep -Fq "$signal" "$log"; then
    printf 'FAIL forbidden route lacked its expected guard signal (%s): %s\n' \
      "$signal" "$label" >&2
    tail -80 "$log" >&2
    exit 1
  fi
  if cmp -s "$baseline_log" "$log"; then
    printf 'FAIL forbidden route left the frozen battery unchanged: %s\n' \
      "$label" >&2
    exit 1
  fi
  printf 'PASS frozen absence guard rejected forbidden route: %s\n' "$label"
}

expect_forbidden_route_rejected \
  custom-row-order \
  "$fixture_root/custom-row-order.lean.txt" \
  'Effect4.RowOrder'

expect_forbidden_route_rejected \
  unchecked-of-list \
  "$fixture_root/unchecked-of-list.lean.txt" \
  'Effect4.Row.ofList'

expect_forbidden_route_rejected \
  append-route \
  "$fixture_root/append-route.lean.txt" \
  'Effect4.Row.append'

expect_forbidden_route_rejected \
  denotation-claim \
  "$fixture_root/denotation-claim.lean.txt" \
  'Effect4.Row.normalization_preserves_denotation'

printf 'PASS Data.Row red-phase reaction gate killed 4/4 forbidden public routes\n'
printf 'NOTE bounded surface reactions only; semantic mutants wait for the green implementation\n'
