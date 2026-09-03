#!/usr/bin/env bash
# Drift gate for generated/lowering-coverage.tsv. --dry-run <candidate.tsv>
# compares the regeneration with a candidate instead (self-test only).
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
committed="$repo_root/generated/lowering-coverage.tsv"; note=""
if [ "${1:-}" = "--dry-run" ]; then committed="$2"; note=" (dry run, closes nothing)"; fi
tmp="$(mktemp "${TMPDIR:-/tmp}/effect4-lowering.XXXXXX")"; trap 'rm -f -- "$tmp"' EXIT
"$repo_root/scripts/generate-lowering-coverage.sh" > "$tmp"
if ! cmp -s "$tmp" "$committed"; then
  echo "FAIL stale generated lowering coverage: $committed" >&2
  diff -u "$committed" "$tmp" | head -30 >&2 || true; exit 1
fi
counts="$(grep $'^count\t' "$tmp" | awk -F'\t' '{ printf "%s %s ", $2, $3 }')"
echo "PASS generated/lowering-coverage.tsv is current; states: ${counts}$note"
