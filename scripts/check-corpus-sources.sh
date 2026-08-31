#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
default_manifest="$repo_root/test/port/corpus/SOURCES.tsv"
manifest="$default_manifest"
corpus_root=""
expected_count=34

usage() {
  echo "usage: scripts/check-corpus-sources.sh --corpus-root PATH [--manifest FILE]" >&2
}

fail() {
  echo "corpus source check failed: $*" >&2
  exit 1
}

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --corpus-root)
      [[ $# -ge 2 ]] || { usage; fail "--corpus-root requires a path"; }
      corpus_root="$2"
      shift 2
      ;;
    --manifest)
      [[ $# -ge 2 ]] || { usage; fail "--manifest requires a file"; }
      manifest="$2"
      shift 2
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      usage
      fail "unknown argument: $1"
      ;;
  esac
done

[[ -n "$corpus_root" ]] || { usage; fail "--corpus-root is required"; }
[[ -d "$corpus_root" && ! -L "$corpus_root" ]] || fail "corpus root is missing, not a directory, or a symlink"
corpus_root="$(cd "$corpus_root" && pwd -P)"
[[ -f "$manifest" && ! -L "$manifest" ]] || fail "source manifest is missing, not a regular file, or a symlink"
manifest="$(cd "$(dirname "$manifest")" && pwd -P)/$(basename "$manifest")"

tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/effect4-corpus-sources.XXXXXX")"
cleanup() {
  rm -rf -- "$tmp_root"
}
trap cleanup EXIT

header=$'checkout\thead_commit\troot_tree\tsource_url\trole\tdisposition'
IFS= read -r observed_header < "$manifest" || fail "source manifest is empty"
[[ "$observed_header" == "$header" ]] || fail "source manifest header is invalid"

if ! awk -F '\t' -v expected="$expected_count" '
  NR == 1 { next }
  NF != 6 { printf "manifest row %d has %d fields, expected 6\n", NR, NF > "/dev/stderr"; exit 20 }
  $1 == "" { printf "manifest row %d has a blank checkout\n", NR > "/dev/stderr"; exit 21 }
  $2 == "" { printf "manifest row %d has a blank HEAD pin\n", NR > "/dev/stderr"; exit 22 }
  $3 == "" { printf "manifest row %d has a blank root-tree pin\n", NR > "/dev/stderr"; exit 23 }
  $4 == "" { printf "manifest row %d has a blank source URL\n", NR > "/dev/stderr"; exit 24 }
  $5 == "" { printf "manifest row %d has a blank role\n", NR > "/dev/stderr"; exit 25 }
  $6 == "" { printf "manifest row %d has a blank disposition\n", NR > "/dev/stderr"; exit 26 }
  { rows += 1 }
  END {
    if (rows != expected) {
      printf "manifest has %d source rows, expected %d\n", rows, expected > "/dev/stderr"
      exit 27
    }
  }
' "$manifest"; then
  fail "source manifest structure is invalid"
fi

manifest_names="$tmp_root/manifest-names"
sorted_names="$tmp_root/sorted-names"
tail -n +2 "$manifest" | cut -f1 > "$manifest_names"

safe_checkout() {
  [[ "$1" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ && "$1" != "." && "$1" != ".." ]]
}

while IFS= read -r checkout; do
  safe_checkout "$checkout" || fail "unsafe checkout name: $checkout"
done < "$manifest_names"

LC_ALL=C sort "$manifest_names" > "$sorted_names"
cmp -s "$manifest_names" "$sorted_names" || fail "source manifest checkouts are not sorted"
[[ "$(LC_ALL=C sort -u "$manifest_names" | wc -l | tr -d '[:space:]')" == "$expected_count" ]] ||
  fail "source manifest contains a duplicate checkout"

duplicate_url="$(awk -F '\t' 'NR > 1 && $4 != "-" { if (seen[$4]++) { print $4; exit } }' "$manifest")"
[[ -z "$duplicate_url" ]] || fail "source manifest contains a duplicate source URL"
duplicate_pin="$(awk -F '\t' 'NR > 1 { pin = $2 FS $3; if (seen[pin]++) { print $2; exit } }' "$manifest")"
[[ -z "$duplicate_pin" ]] || fail "source manifest contains a duplicate commit/tree pin"

actual_names="$tmp_root/actual-names"
: > "$actual_names"
while IFS= read -r -d '' entry; do
  git_marker="$entry/.git"
  if [[ -d "$git_marker" || -f "$git_marker" || -L "$git_marker" ]]; then
    [[ ! -L "$entry" ]] || fail "checkout is a symlink: $(basename "$entry")"
    [[ -d "$git_marker" && ! -L "$git_marker" ]] || fail "checkout Git metadata is not a local directory: $(basename "$entry")"
    basename "$entry" >> "$actual_names"
  fi
done < <(find -P "$corpus_root" -mindepth 1 -maxdepth 1 -print0)
LC_ALL=C sort -o "$actual_names" "$actual_names"

if ! cmp -s "$manifest_names" "$actual_names"; then
  diff -u "$manifest_names" "$actual_names" >&2 || true
  fail "checkout set mismatch (absent, unrecorded, or extra checkout)"
fi

while IFS=$'\t' read -r checkout head_commit root_tree source_url role disposition; do
  safe_checkout "$checkout" || fail "unsafe checkout name: $checkout"
  [[ "$head_commit" =~ ^[0-9a-f]{40}$ ]] || fail "invalid HEAD pin for $checkout"
  [[ "$root_tree" =~ ^[0-9a-f]{40}$ ]] || fail "invalid root-tree pin for $checkout"
  [[ "$source_url" == "-" || "$source_url" =~ ^[^[:space:]]+$ ]] || fail "invalid source URL for $checkout"
  [[ "$role" =~ ^[a-z0-9][a-z0-9-]*$ ]] || fail "invalid role for $checkout"
  [[ "$disposition" =~ ^[a-z0-9][a-z0-9-]*$ ]] || fail "invalid disposition for $checkout"

  checkout_root="$corpus_root/$checkout"
  [[ -d "$checkout_root" && ! -L "$checkout_root" ]] || fail "checkout is absent or a symlink: $checkout"
  [[ -d "$checkout_root/.git" && ! -L "$checkout_root/.git" ]] || fail "checkout Git metadata is not a local directory: $checkout"
  canonical_checkout="$(cd "$checkout_root" && pwd -P)"
  [[ "$(dirname "$canonical_checkout")" == "$corpus_root" && "$(basename "$canonical_checkout")" == "$checkout" ]] ||
    fail "checkout escapes the corpus root: $checkout"
  [[ "$(git -C "$checkout_root" rev-parse --show-toplevel 2>/dev/null)" == "$canonical_checkout" ]] ||
    fail "checkout is not a top-level Git worktree: $checkout"

  observed_head="$(git -C "$checkout_root" rev-parse --verify HEAD 2>/dev/null)" || fail "cannot resolve HEAD for $checkout"
  [[ "$observed_head" == "$head_commit" ]] || fail "HEAD pin mismatch for $checkout"
  observed_tree="$(git -C "$checkout_root" rev-parse --verify 'HEAD^{tree}' 2>/dev/null)" || fail "cannot resolve root tree for $checkout"
  [[ "$observed_tree" == "$root_tree" ]] || fail "root-tree pin mismatch for $checkout"
  git -C "$checkout_root" cat-file -e "$head_commit^{commit}" 2>/dev/null || fail "HEAD pin is not a commit for $checkout"
  git -C "$checkout_root" cat-file -e "$root_tree^{tree}" 2>/dev/null || fail "root-tree pin is not a tree for $checkout"

  tracked_status="$(git -C "$checkout_root" status --porcelain=v1 --untracked-files=no)"
  [[ -z "$tracked_status" ]] || fail "tracked files are dirty in $checkout"

  if observed_url="$(git -C "$checkout_root" remote get-url origin 2>/dev/null)"; then
    [[ "$source_url" != "-" ]] || fail "origin URL is discoverable but unrecorded for $checkout"
    [[ "$observed_url" == "$source_url" ]] || fail "origin URL mismatch for $checkout"
  else
    [[ "$source_url" == "-" ]] || fail "recorded origin URL is not discoverable for $checkout"
  fi

  tree_manifest="$tmp_root/$checkout.ls-tree"
  LC_ALL=C git -C "$checkout_root" ls-tree -r -z --full-tree "$head_commit" > "$tree_manifest"
  entry_count="$(LC_ALL=C git -C "$checkout_root" ls-tree -r --full-tree --format='%(objectname)' "$head_commit" | wc -l | tr -d '[:space:]')"
  tree_digest="$(sha256_file "$tree_manifest")"
  printf 'PASS corpus source: checkout=%s entries=%s tree_manifest_sha256=%s\n' "$checkout" "$entry_count" "$tree_digest"
done < <(tail -n +2 "$manifest")

sources_digest="$(sha256_file "$manifest")"
printf 'PASS corpus inventory: sources=%s sources_sha256=%s\n' "$expected_count" "$sources_digest"
echo "PASS checkout set, pins, trees, tracked cleanliness, origins, and path boundary"
