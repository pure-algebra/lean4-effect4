#!/usr/bin/env bash
# Prints the one sanctioned Effect runtime coverage report, from the emitted
# facts of Test/Audit/RuntimeCoverage.lean. See docs/RUNTIME-COVERAGE.md.
# Never hand-type these numbers; run this script and paste its output.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
coverage_rel="Test/Audit/RuntimeCoverage.lean"

if [[ $# -ne 0 ]]; then
  printf 'usage: report-effect-runtime-coverage.sh\n' >&2
  exit 2
fi

lake_bin="$(command -v lake || true)"
[[ -n "$lake_bin" ]] || { printf 'FAIL lake is unavailable\n' >&2; exit 1; }

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-runtime-coverage-report.XXXXXX")"
cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-runtime-coverage-report.*) rm -rf -- "$tmp_root" ;;
    *) printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2; cleanup_rc=1 ;;
  esac
  exit "$cleanup_rc"
}
trap cleanup EXIT

(
  cd -- "$repo_root"
  unset LEAN_PATH LEAN_SRC_PATH
  "$lake_bin" build Test.Audit.RuntimeCoverage >"$tmp_root/build.log" 2>&1
  "$lake_bin" env lean "$coverage_rel" >"$tmp_root/coverage.log" 2>&1
) || {
  printf 'FAIL runtime coverage module did not build; no report can be issued\n' >&2
  cat "$tmp_root/build.log" "$tmp_root/coverage.log" >&2 2>/dev/null || true
  exit 1
}

grep $'^E4RTCOV\t' "$tmp_root/coverage.log" | sed 's/^E4RTCOV\t//' >"$tmp_root/evidence.tsv"
coverage_row="$(awk -F '\t' '$1 == "coverage" { print; exit }' "$tmp_root/evidence.tsv")"
[[ -n "$coverage_row" ]] || {
  printf 'FAIL runtime coverage module emitted no coverage row\n' >&2
  exit 1
}
IFS=$'\t' read -r _ total denominator owned_green green partial absent <<<"$coverage_row"
excluded=$((total - denominator))
partial_ids="$(awk -F '\t' '$1 == "row" && $5 == "partial" { print $2 }' "$tmp_root/evidence.tsv" | paste -sd ' ' -)"
commit="$(cd -- "$repo_root" && git rev-parse --short HEAD 2>/dev/null || printf 'unknown')"
dirty=""
if [[ -n "$(cd -- "$repo_root" && git status --porcelain -- src Test generated scripts vendor 2>/dev/null)" ]]; then
  dirty=" (working tree has uncommitted changes)"
fi

printf 'Effect rc.112 runtime coverage: denominator %s; owned-with-green %s/%s;\n' \
  "$denominator" "$owned_green" "$denominator"
printf 'green %s, partial %s, absent %s; census %s rows, %s excluded\n' \
  "$green" "$partial" "$absent" "$total" "$excluded"
printf 'partial: %s\n' "${partial_ids:-none}"
printf 'produced at %s%s by scripts/report-effect-runtime-coverage.sh\n' "$commit" "$dirty"
