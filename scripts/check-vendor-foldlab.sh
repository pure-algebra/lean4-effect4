#!/usr/bin/env bash
set -euo pipefail

default_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
repo_root="${1:-$default_root}"
repo_root="$(cd "$repo_root" && pwd)"
vendor_root="$repo_root/vendor/foldlab"
expected_pin="feb29321fd50204aa338209d313e84a3f8b71c66"

fail() {
  echo "foldlab vendor check failed: $*" >&2
  exit 1
}

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

[[ -d "$vendor_root" ]] || fail "missing vendor/foldlab"
pin="$(tr -d '\r\n' < "$vendor_root/PIN")"
[[ "$pin" == "$expected_pin" ]] || fail "pin is $pin, expected $expected_pin"

expected_scopes="$(printf '%s\n' \
  'library/cas' \
  'library/effects' \
  'library/effect-protocol' \
  '.staging/effect-core-v1' \
  'formal/effect-core-v1' \
  'docs/effect-typescript-semantics' \
  'docs/effect-replay' \
  'LICENSE')"
actual_scopes="$(tr -d '\r' < "$vendor_root/SCOPE.txt")"
[[ "$actual_scopes" == "$expected_scopes" ]] || fail "SCOPE.txt differs from the frozen extraction scope"

tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/effect4-check-foldlab.XXXXXX")"
cleanup() {
  rm -rf -- "$tmp_root"
}
trap cleanup EXIT

allowed_pinned_path() {
  case "$1" in
    LICENSE|library/cas/*|library/effects/*|library/effect-protocol/*|.staging/effect-core-v1/*|formal/effect-core-v1/*|docs/effect-typescript-semantics/*|docs/effect-replay/*) return 0 ;;
    *) return 1 ;;
  esac
}

safe_source_path() {
  case "$1" in
    ''|/*|..|../*|*/..|*/../*) return 1 ;;
    *) return 0 ;;
  esac
}

check_manifest() {
  local label="$1"
  local tree_root="$2"
  local manifest="$3"
  local expected_count="$4"
  local expected_paths="$tmp_root/$label-expected"
  local actual_paths="$tmp_root/$label-actual"
  local sorted_paths="$tmp_root/$label-sorted"
  local header
  local source_path bytes digest git_blob extra source_file actual_bytes actual_digest actual_blob

  [[ -d "$tree_root" ]] || fail "$label tree is missing"
  [[ -f "$manifest" ]] || fail "$label manifest is missing"
  IFS= read -r header < "$manifest"
  [[ "$header" == $'source_path\tbytes\tsha256\tgit_blob' ]] || fail "$label manifest header is invalid"

  tail -n +2 "$manifest" | cut -f1 > "$expected_paths"
  LC_ALL=C sort "$expected_paths" > "$sorted_paths"
  cmp -s "$expected_paths" "$sorted_paths" || fail "$label manifest paths are not sorted"
  [[ "$(LC_ALL=C sort -u "$expected_paths" | wc -l | tr -d '[:space:]')" == "$(wc -l < "$expected_paths" | tr -d '[:space:]')" ]] ||
    fail "$label manifest contains duplicate paths"
  [[ "$(wc -l < "$expected_paths" | tr -d '[:space:]')" == "$expected_count" ]] ||
    fail "$label manifest count differs from $expected_count"

  find "$tree_root" \( -type f -o -type l \) -print |
    while IFS= read -r source_file; do
      printf '%s\n' "${source_file#"$tree_root/"}"
    done | LC_ALL=C sort > "$actual_paths"
  if ! cmp -s "$expected_paths" "$actual_paths"; then
    diff -u "$expected_paths" "$actual_paths" >&2 || true
    fail "$label file-set mismatch (omission or extra file)"
  fi

  while IFS=$'\t' read -r source_path bytes digest git_blob extra; do
    [[ -z "${extra:-}" ]] || fail "$label manifest has extra fields at $source_path"
    safe_source_path "$source_path" || fail "$label manifest has unsafe path: $source_path"
    [[ "$bytes" =~ ^[0-9]+$ ]] || fail "$label byte count is invalid at $source_path"
    [[ "$digest" =~ ^[0-9a-f]{64}$ ]] || fail "$label SHA-256 is invalid at $source_path"
    if [[ "$label" == "pinned" ]]; then
      allowed_pinned_path "$source_path" || fail "pinned path is outside SCOPE.txt: $source_path"
      [[ "$git_blob" =~ ^[0-9a-f]{40}$ ]] || fail "pinned Git blob is invalid at $source_path"
    else
      [[ "$git_blob" == "-" ]] || fail "late evidence invents a Git blob at $source_path"
    fi
    source_file="$tree_root/$source_path"
    [[ -f "$source_file" && ! -L "$source_file" ]] || fail "$label path is not a regular file: $source_path"
    actual_bytes="$(wc -c < "$source_file" | tr -d '[:space:]')"
    [[ "$actual_bytes" == "$bytes" ]] || fail "$label byte-size mismatch at $source_path"
    actual_digest="$(sha256_file "$source_file")"
    [[ "$actual_digest" == "$digest" ]] || fail "$label SHA-256 mismatch at $source_path"
    if [[ "$label" == "pinned" ]]; then
      actual_blob="$(git hash-object "$source_file")"
      [[ "$actual_blob" == "$git_blob" ]] || fail "pinned Git-blob mismatch at $source_path"
    fi
  done < <(tail -n +2 "$manifest")
}

check_manifest pinned "$vendor_root/pinned/tree" "$vendor_root/PINNED-MANIFEST.tsv" 826
check_manifest late "$vendor_root/late/tree" "$vendor_root/LATE-MANIFEST.tsv" 85

late_paths="$tmp_root/late-paths"
tail -n +2 "$vendor_root/LATE-MANIFEST.tsv" | cut -f1 > "$late_paths"
late_lean_count="$(grep -cE '^\.staging/effect-core-v1/workshop/(s1|s2|layer)/[^/]+\.lean$' "$late_paths" || true)"
s1_count="$(grep -cE '^\.staging/effect-core-v1/workshop/s1/[^/]+\.lean$' "$late_paths" || true)"
s2_count="$(grep -cE '^\.staging/effect-core-v1/workshop/s2/[^/]+\.lean$' "$late_paths" || true)"
layer_count="$(grep -cE '^\.staging/effect-core-v1/workshop/layer/[^/]+\.lean$' "$late_paths" || true)"
ground_count="$(grep -cE '^\.staging/effect-core-v1/workshop/layer/ground-[^/]+\.md$' "$late_paths" || true)"
report_count="$(grep -cE '^\.staging/agent-reports/2026-08-31-effect-core-(s1-slice|s2-slice|layer-design)\.md$' "$late_paths" || true)"
if [[ "$late_lean_count" != "79" || "$s1_count" != "39" || "$s2_count" != "24" || "$layer_count" != "16" || "$ground_count" != "3" || "$report_count" != "3" ]]; then
  fail "late evidence categories differ: lean=$late_lean_count s1=$s1_count s2=$s2_count layer=$layer_count ground=$ground_count reports=$report_count"
fi

for dependency_file in "$repo_root/lakefile.toml" "$repo_root/lake-manifest.json"; do
  if [[ -f "$dependency_file" ]] && grep -qi 'foldlab' "$dependency_file"; then
    fail "Foldlab appears in a Lake dependency file: ${dependency_file#"$repo_root/"}"
  fi
done

pinned_bytes="$(awk -F '\t' 'NR > 1 { total += $2 } END { printf "%.0f", total }' "$vendor_root/PINNED-MANIFEST.tsv")"
late_bytes="$(awk -F '\t' 'NR > 1 { total += $2 } END { printf "%.0f", total }' "$vendor_root/LATE-MANIFEST.tsv")"
echo "PASS pinned: 826 files, $pinned_bytes bytes, commit $expected_pin"
echo "PASS late evidence: 85 files, $late_bytes bytes (79 Lean, 3 research notes, 3 reports)"
echo "PASS total evidence payload: 911 files, $((pinned_bytes + late_bytes)) bytes"
echo "PASS closed inventories, byte hashes, Git blobs, and dependency boundary"
