#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
vendor_root="$repo_root/vendor/foldlab"
foldlab_checkout="${1:-}"

if [[ -z "$foldlab_checkout" || "$foldlab_checkout" == "-h" || "$foldlab_checkout" == "--help" ]]; then
  echo "usage: $0 /path/to/foldlab" >&2
  exit 64
fi

foldlab_checkout="$(cd "$foldlab_checkout" && pwd)"
if [[ "$(git -C "$foldlab_checkout" rev-parse --is-inside-work-tree 2>/dev/null || true)" != "true" ]]; then
  echo "not a Git worktree: $foldlab_checkout" >&2
  exit 1
fi

pin="$(tr -d '\r\n' < "$vendor_root/PIN")"
expected_pin="feb29321fd50204aa338209d313e84a3f8b71c66"
if [[ "$pin" != "$expected_pin" ]]; then
  echo "unexpected Foldlab pin: $pin" >&2
  exit 1
fi
if ! git -C "$foldlab_checkout" cat-file -e "$pin^{commit}" 2>/dev/null; then
  echo "Foldlab commit is unavailable in $foldlab_checkout: $pin" >&2
  exit 1
fi

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/effect4-vendor-foldlab.XXXXXX")"
cleanup() {
  rm -rf -- "$tmp_root"
}
trap cleanup EXIT

mkdir -p "$tmp_root/pinned-tree" "$tmp_root/late-tree"

scopes=()
while IFS= read -r scope; do
  [[ -n "$scope" ]] && scopes+=("$scope")
done < "$vendor_root/SCOPE.txt"

git -C "$foldlab_checkout" archive "$pin" -- "${scopes[@]}" |
  tar -xf - -C "$tmp_root/pinned-tree"

printf 'source_path\tbytes\tsha256\tgit_blob\n' > "$tmp_root/PINNED-MANIFEST.tsv"
git -C "$foldlab_checkout" ls-tree -r "$pin" -- "${scopes[@]}" > "$tmp_root/pinned-ls-tree"
while IFS=$'\t' read -r metadata source_path; do
  read -r mode object_type git_blob <<< "$metadata"
  if [[ "$object_type" != "blob" ]]; then
    echo "unsupported pinned Git object at $source_path: $object_type" >&2
    exit 1
  fi
  source_file="$tmp_root/pinned-tree/$source_path"
  if [[ ! -f "$source_file" || -L "$source_file" ]]; then
    echo "archive did not produce a regular file: $source_path" >&2
    exit 1
  fi
  actual_blob="$(git hash-object "$source_file")"
  if [[ "$actual_blob" != "$git_blob" ]]; then
    echo "archive blob mismatch: $source_path" >&2
    exit 1
  fi
  bytes="$(wc -c < "$source_file" | tr -d '[:space:]')"
  digest="$(sha256_file "$source_file")"
  printf '%s\t%s\t%s\t%s\n' "$source_path" "$bytes" "$digest" "$git_blob" \
    >> "$tmp_root/PINNED-MANIFEST.tsv"
done < "$tmp_root/pinned-ls-tree"

late_sources="$tmp_root/late-sources"
{
  find \
    "$foldlab_checkout/.staging/effect-core-v1/workshop/s1" \
    "$foldlab_checkout/.staging/effect-core-v1/workshop/s2" \
    "$foldlab_checkout/.staging/effect-core-v1/workshop/layer" \
    -maxdepth 1 -type f -name '*.lean' -print
  find "$foldlab_checkout/.staging/effect-core-v1/workshop/layer" \
    -maxdepth 1 -type f -name 'ground-*.md' -print
  printf '%s\n' \
    "$foldlab_checkout/.staging/agent-reports/2026-08-31-effect-core-s1-slice.md" \
    "$foldlab_checkout/.staging/agent-reports/2026-08-31-effect-core-s2-slice.md" \
    "$foldlab_checkout/.staging/agent-reports/2026-08-31-effect-core-layer-design.md"
} | LC_ALL=C sort > "$late_sources"

late_count="$(wc -l < "$late_sources" | tr -d '[:space:]')"
late_lean_count="$(grep -cE '/workshop/(s1|s2|layer)/[^/]+\.lean$' "$late_sources" || true)"
late_ground_count="$(grep -cE '/workshop/layer/ground-[^/]+\.md$' "$late_sources" || true)"
late_report_count="$(grep -cE '/agent-reports/2026-08-31-effect-core-(s1-slice|s2-slice|layer-design)\.md$' "$late_sources" || true)"
if [[ "$late_count" != "85" || "$late_lean_count" != "79" || "$late_ground_count" != "3" || "$late_report_count" != "3" ]]; then
  echo "late evidence shape mismatch: total=$late_count lean=$late_lean_count ground=$late_ground_count reports=$late_report_count" >&2
  exit 1
fi

printf 'source_path\tbytes\tsha256\tgit_blob\n' > "$tmp_root/LATE-MANIFEST.tsv"
while IFS= read -r source_file; do
  if [[ ! -f "$source_file" || -L "$source_file" ]]; then
    echo "late evidence is unavailable or not a regular file: $source_file" >&2
    exit 1
  fi
  source_path="${source_file#"$foldlab_checkout/"}"
  destination="$tmp_root/late-tree/$source_path"
  mkdir -p "$(dirname "$destination")"
  cp -p "$source_file" "$destination"
  bytes="$(wc -c < "$destination" | tr -d '[:space:]')"
  digest="$(sha256_file "$destination")"
  printf '%s\t%s\t%s\t-\n' "$source_path" "$bytes" "$digest" \
    >> "$tmp_root/LATE-MANIFEST.tsv"
done < "$late_sources"

pinned_count="$(($(wc -l < "$tmp_root/PINNED-MANIFEST.tsv") - 1))"
if [[ "$pinned_count" != "826" ]]; then
  echo "pinned inventory mismatch: expected 826 files, found $pinned_count" >&2
  exit 1
fi

if [[ "$vendor_root" != "$repo_root/vendor/foldlab" ]]; then
  echo "refusing unsafe vendor destination: $vendor_root" >&2
  exit 1
fi
mkdir -p "$vendor_root/pinned" "$vendor_root/late"
rm -rf -- "$vendor_root/pinned/tree" "$vendor_root/late/tree"
mv "$tmp_root/pinned-tree" "$vendor_root/pinned/tree"
mv "$tmp_root/late-tree" "$vendor_root/late/tree"
mv "$tmp_root/PINNED-MANIFEST.tsv" "$vendor_root/PINNED-MANIFEST.tsv"
mv "$tmp_root/LATE-MANIFEST.tsv" "$vendor_root/LATE-MANIFEST.tsv"

"$repo_root/scripts/check-vendor-foldlab.sh"
