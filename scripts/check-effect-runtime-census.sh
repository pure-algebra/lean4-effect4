#!/usr/bin/env bash
# Byte-for-byte drift gate for the Effect v4 runtime mechanism census, and the
# join between that census and the Lean witnesses in
# Test/Audit/RuntimeCoverage.lean.
#
# ## Stamp (rule 9)
#
# The generator reads twelve vendored rc.112 sources, and the projection names
# them itself: every `input` row of `generated/effect-runtime-census.tsv` is one
# of those paths with its expected digest. So the key is read out of the
# candidate rather than re-spelled here, which is also what keeps it honest --
# a doctored input list changes the candidate, and the candidate is in the key.
# When a real pinned install is reachable the generator additionally compares
# each vendored file with its installed counterpart, so those twelve paths are
# named too; absent, as they are in CI, they contribute `absent` and the key is
# stable. The rest is the witness module and the Lake traces of its imports,
# taken after `lake build Test.Audit.RuntimeCoverage`, the toolchain and
# the manifest.
#
# `--dry-run` reports on a candidate and closes nothing, so it neither reads nor
# writes a stamp.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
. "$repo_root/scripts/lib/portable.sh"
. "$repo_root/scripts/lib/stamp.sh"
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

# 0. The stamp. The witness module is built first so that the traces the key
#    hashes are the ones the join will read; step 2 builds it again, for free.
stamped=0
if [[ "$mode" == "production" ]]; then
  stamped=1
  (
    cd -- "$repo_root"
    unset LEAN_PATH LEAN_SRC_PATH
    "$lake_bin" build Test.Audit.RuntimeCoverage >"$tmp_root/stamp-build.log" 2>&1
  ) || {
    printf 'FAIL Test.Audit.RuntimeCoverage does not build\n' >&2
    cat "$tmp_root/stamp-build.log" >&2
    exit 1
  }
  installed_src="${EFFECT4_EFFECT_NODE_MODULES:-$repo_root/../foldlab/library/effects/node_modules}/effect"
  census_inputs=(
    "$repo_root/scripts/check-effect-runtime-census.sh"
    "$generator"
    "$repo_root/scripts/lib/portable.sh"
    "$repo_root/scripts/lib/stamp.sh"
    "$repo_root/$coverage_rel"
    "$stamp_build_lib/Test/Audit/RuntimeCoverage.trace"
    "$candidate"
    "$installed_src/package.json"
    "$repo_root/lakefile.toml"
    "$repo_root/lake-manifest.json"
    "$repo_root/lean-toolchain"
  )
  # The `input` rows of the projection name the twelve vendored rc.112 sources
  # the generator extracts spans from; each is paired with the installed copy
  # the generator cross-checks it against when one is reachable.
  while IFS= read -r pinned_rel; do
    [[ -n "$pinned_rel" ]] || continue
    census_inputs+=("$repo_root/$pinned_rel" "$installed_src/src/${pinned_rel#*/src/}")
  done < <(awk -F '\t' '$1 == "input" { print $2 }' "$candidate")
  while IFS= read -r trace; do
    census_inputs+=("$trace")
  done < <(stamp_lean_traces "$repo_root/$coverage_rel")
  census_key="$(stamp_key "${census_inputs[@]}")"
  if stamp_hit effect-runtime-census "$census_key"; then
    stamp_report effect-runtime-census "$census_key"
    exit 0
  fi
fi

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
  "$lake_bin" env lean "$coverage_rel" >"$tmp_root/coverage.log" 2>&1
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

# 5. Every witness must have a frozen statement ascription in the module
#    source, in the same order as the emitted snapshot list. This is what stops
#    a witness from silently losing its exact statement.
awk 'match($0, /^#check \(@[A-Za-z0-9_.?]+ :/) {
  line = substr($0, RSTART + 9)
  sub(/ :.*$/, "", line)
  print line
}' "$repo_root/$coverage_rel" >"$tmp_root/source.snapshot"
awk -F '\t' '$1 == "snapshot" { print $2 }' "$tmp_root/evidence.tsv" >"$tmp_root/emitted.snapshot"
if ! cmp -s -- "$tmp_root/source.snapshot" "$tmp_root/emitted.snapshot"; then
  printf 'FAIL frozen statement ascriptions do not match the emitted snapshot list\n' >&2
  diff -u -- "$tmp_root/source.snapshot" "$tmp_root/emitted.snapshot" >&2 || true
  exit 1
fi

# 6. Witness kernel receipts stay inside the semantic ceiling. Classical.choice
#    is admissible for audit metaprogramming, never for a semantic witness.
invalid_axiom_rows="$(awk -F '\t' \
  '$1 == "witness" && $4 != "none" && $4 != "propext" && \
   $4 != "Quot.sound" && $4 != "propext,Quot.sound" { count++ } \
   END { print count + 0 }' "$tmp_root/evidence.tsv")"
[[ "$invalid_axiom_rows" == 0 ]] || {
  printf 'FAIL runtime coverage emitted %s witness rows outside the semantic axiom ceiling\n' \
    "$invalid_axiom_rows" >&2
  awk -F '\t' '$1 == "witness" && $4 != "none" && $4 != "propext" && $4 != "Quot.sound" && $4 != "propext,Quot.sound"' \
    "$tmp_root/evidence.tsv" >&2
  exit 1
}

# 7. Declared witness counts must equal the emitted witness rows per id.
awk -F '\t' '$1 == "row" && $6 + 0 > 0 { print $2 "\t" $6 }' "$tmp_root/evidence.tsv" \
  | sort >"$tmp_root/declared.counts"
awk -F '\t' '$1 == "witness" { n[$2]++ } END { for (id in n) print id "\t" n[id] }' \
  "$tmp_root/evidence.tsv" | sort >"$tmp_root/actual.counts"
if ! cmp -s -- "$tmp_root/declared.counts" "$tmp_root/actual.counts"; then
  printf 'FAIL declared witness counts do not match emitted witness rows\n' >&2
  diff -u -- "$tmp_root/declared.counts" "$tmp_root/actual.counts" >&2 || true
  exit 1
fi

# 8. The coverage summary must be arithmetically consistent with the rows.
coverage_row="$(awk -F '\t' '$1 == "coverage" { print; exit }' "$tmp_root/evidence.tsv")"
[[ -n "$coverage_row" ]] || {
  printf 'FAIL runtime coverage emitted no coverage summary row\n' >&2
  exit 1
}
IFS=$'\t' read -r _ total denominator owned_green green partial absent <<<"$coverage_row"
census_total="$(wc -l <"$tmp_root/census.ids" | tr -d ' ')"
[[ "$total" == "$census_total" ]] || {
  printf 'FAIL coverage total %s does not match the %s census rows\n' "$total" "$census_total" >&2
  exit 1
}
[[ $((green + partial + absent)) == "$denominator" ]] || {
  printf 'FAIL coverage states %s+%s+%s do not sum to the denominator %s\n' \
    "$green" "$partial" "$absent" "$denominator" >&2
  exit 1
}
[[ "$owned_green" -le "$green" ]] || {
  printf 'FAIL owned-with-green %s exceeds green %s\n' "$owned_green" "$green" >&2
  exit 1
}

if [[ "$mode" == "dry-run" ]]; then
  printf 'PASS dry-run candidate matches the pinned Effect runtime census; closes nothing\n'
else
  if [[ "$stamped" -eq 1 ]]; then
    stamp_write effect-runtime-census "$census_key" \
      "$(printf '%s mechanism rows joined; denominator %s, owned-with-green %s, green %s, partial %s, absent %s' \
        "$census_total" "$denominator" "$owned_green" "$green" "$partial" "$absent")"
  fi
  printf 'PASS generated Effect 4.0.0-rc.112 runtime census is current: %s mechanism rows\n' "$census_total"
  printf 'PASS census ids, kinds, statement snapshots and witness receipts join the Lean row list\n'
  printf 'PASS coverage: denominator %s; owned-with-green %s; green %s, partial %s, absent %s\n' \
    "$denominator" "$owned_green" "$green" "$partial" "$absent"
fi
