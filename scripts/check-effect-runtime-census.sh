#!/usr/bin/env bash
# Byte-for-byte drift gate for the Effect v4 runtime mechanism census, and the
# join between that census and the Lean witnesses in
# Test/Audit/RuntimeCoverage.lean: the census is what the generator emits from
# the vendored rc.112 sources, the Lean module builds and emits its rows, and the
# two carry the same ids with the same kinds. Whether a witness exists and is a
# theorem is the module's own check; the axiom ceiling is the gate's.
#
# `--dry-run` reports on a candidate instead of the committed census.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
. "$repo_root/scripts/lib/portable.sh"
generator="$repo_root/scripts/generate-effect-runtime-census.sh"
fixed_projection="$repo_root/generated/effect-runtime-census.tsv"
coverage_rel="Test/Audit/RuntimeCoverage.lean"

mode="production"
candidate="$fixed_projection"
if [[ $# -gt 0 && "$1" == "--force" ]]; then
  export EFFECT4_FORCE=1
  shift
fi
if [[ $# -gt 0 ]]; then
  if [[ $# -eq 2 && "$1" == "--dry-run" ]]; then
    mode="dry-run"
    candidate="$2"
  else
    printf 'usage: check-effect-runtime-census.sh [--force] [--dry-run <candidate.tsv>]\n' >&2
    exit 2
  fi
fi

if [[ -n "${EFFECT4_RUNTIME_CENSUS_CANDIDATE-}" ]]; then
  printf 'FAIL runtime census gate rejects environment candidate overrides\n' >&2
  exit 2
fi

[[ -x "$generator" ]] || {
  printf 'FAIL generator is not executable: %s\n' "$generator" >&2
  exit 1
}
[[ -f "$candidate" && ! -L "$candidate" ]] || {
  printf 'FAIL runtime census candidate is absent, not regular, or a symlink: %s\n' \
    "$candidate" >&2
  exit 1
}
[[ -f "$repo_root/$coverage_rel" && ! -L "$repo_root/$coverage_rel" ]] || {
  printf 'FAIL runtime coverage module is absent, not regular, or a symlink: %s\n' \
    "$repo_root/$coverage_rel" >&2
  exit 1
}

lake_bin="$(command -v lake || true)"
[[ -n "$lake_bin" ]] || { printf 'FAIL lake is unavailable\n' >&2; exit 1; }

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-runtime-census-check.XXXXXX")"

cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-runtime-census-check.*) rm -rf -- "$tmp_root" ;;
    *)
      printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2
      cleanup_rc=1
      ;;
  esac
  exit "$cleanup_rc"
}
trap cleanup EXIT

# 1. The census must be byte-identical to a fresh extraction from the pinned
#    Effect source. The generator fails on its own before reaching here if a
#    pinned digest or an anchor drifted.
"$generator" >"$tmp_root/fresh.tsv"

if ! cmp -s -- "$tmp_root/fresh.tsv" "$candidate"; then
  printf 'FAIL stale generated Effect runtime census: %s\n' "$candidate" >&2
  diff -u -- "$candidate" "$tmp_root/fresh.tsv" >&2 || true
  exit 1
fi

# 2. The Lean join must build and emit its frozen rows.
(
  cd -- "$repo_root"
  unset LEAN_PATH LEAN_SRC_PATH
  "$lake_bin" build Test.Audit.RuntimeCoverage >"$tmp_root/build.log" 2>&1
  "$lake_bin" env lean -DwarningAsError=true "$coverage_rel" >"$tmp_root/coverage.log" 2>&1
)

grep $'^E4RTCOV\t' "$tmp_root/coverage.log" >"$tmp_root/evidence.rows" || {
  printf 'FAIL runtime coverage module emitted no evidence rows\n' >&2
  cat "$tmp_root/coverage.log" >&2
  exit 1
}
sed 's/^E4RTCOV\t//' "$tmp_root/evidence.rows" >"$tmp_root/evidence.tsv"

# 3. Census ids and Lean row ids must be the same set, in both directions.
awk -F '\t' '$1 == "mechanism" { print $3 }' "$candidate" | sort >"$tmp_root/census.ids"
awk -F '\t' '$1 == "row" { print $2 }' "$tmp_root/evidence.tsv" | sort >"$tmp_root/lean.ids"
if ! cmp -s -- "$tmp_root/census.ids" "$tmp_root/lean.ids"; then
  printf 'FAIL runtime census ids and RuntimeCoverage row ids differ\n' >&2
  diff -u -- "$tmp_root/census.ids" "$tmp_root/lean.ids" >&2 || true
  exit 1
fi

# 4. The kind recorded in Lean must be the kind the census extracted.
awk -F '\t' '$1 == "mechanism" { print $3 "\t" $2 }' "$candidate" | sort >"$tmp_root/census.kinds"
awk -F '\t' '$1 == "row" { print $2 "\t" $3 }' "$tmp_root/evidence.tsv" | sort >"$tmp_root/lean.kinds"
if ! cmp -s -- "$tmp_root/census.kinds" "$tmp_root/lean.kinds"; then
  printf 'FAIL runtime census kinds and RuntimeCoverage row kinds differ\n' >&2
  diff -u -- "$tmp_root/census.kinds" "$tmp_root/lean.kinds" >&2 || true
  exit 1
fi

# 5. Signed divergences must join in both directions. A signature changes the
# disposition, never the mechanism inventory, denominator, or witness checks.
awk -F '\t' '$1 == "divergence" { print }' "$candidate" | sort >"$tmp_root/census.divergences"
awk -F '\t' '$1 == "divergence" { print }' "$tmp_root/evidence.tsv" | sort >"$tmp_root/lean.divergences"
if ! cmp -s -- "$tmp_root/census.divergences" "$tmp_root/lean.divergences"; then
  printf 'FAIL runtime census signed divergences and Lean dispositions differ\n' >&2
  diff -u -- "$tmp_root/census.divergences" "$tmp_root/lean.divergences" >&2 || true
  exit 1
fi
while IFS=$'\t' read -r _ id ruling witness; do
  [[ -f "$repo_root/$witness" && ! -L "$repo_root/$witness" ]] || {
    printf 'FAIL signed divergence %s (%s) has no executable witness: %s\n' "$id" "$ruling" "$witness" >&2
    exit 1
  }
  awk -F '|' -v finding="$ruling" '$2 == " `" finding "` " { found=1 } END { exit !found }' \
    "$repo_root/docs/UPSTREAM-BACKLOG.md" || {
    printf 'FAIL signed divergence %s has no upstream finding: %s\n' "$id" "$ruling" >&2
    exit 1
  }
  printf 'DIVERGED %s: %s; %s\n' "$id" "$ruling" "$witness"
done <"$tmp_root/census.divergences"

census_total="$(wc -l <"$tmp_root/census.ids" | tr -d ' ')"

if [[ "$mode" == "dry-run" ]]; then
  printf 'PASS dry-run candidate matches the pinned Effect runtime census; closes nothing\n'
else
  printf 'PASS generated Effect 4.0.0-rc.112 runtime census is current: %s mechanism rows\n' "$census_total"
  printf 'PASS census ids and kinds join the Lean row list\n'
fi
