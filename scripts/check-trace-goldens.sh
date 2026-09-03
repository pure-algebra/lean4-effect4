#!/usr/bin/env bash
# Hermetic drift gate: regenerate the Lean-expected traces and compare them
# byte for byte with generated/traces/. Needs no host.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# --dry-run <dir> compares the regeneration with <dir> instead of the committed
# projections; it exists for the mutation self-test and closes nothing.
committed_dir="$repo_root/generated/traces"; note=""
if [ "${1:-}" = "--dry-run" ]; then committed_dir="$2"; note=" (dry run, closes nothing)"; fi
tmp="$(mktemp -d "${TMPDIR:-/tmp}/effect4-traces.XXXXXX")"
trap 'rm -rf -- "$tmp"' EXIT
"$repo_root/scripts/generate-trace-goldens.sh" "$tmp" >/dev/null
status=0
for candidate in "$tmp"/*.tsv; do
  name="$(basename "$candidate")"
  if ! cmp -s "$candidate" "$committed_dir/$name"; then
    echo "FAIL stale generated trace projection: $name" >&2
    diff -u "$committed_dir/$name" "$candidate" | head -20 >&2 || true
    status=1
  fi
done
for committed in "$committed_dir"/*.tsv; do
  [ -f "$tmp/$(basename "$committed")" ] || { echo "FAIL orphan trace projection: $(basename "$committed")" >&2; status=1; }
done
[ "$status" -eq 0 ] && echo "PASS generated/traces is current ($(ls "$tmp" | wc -l | tr -d ' ') files)$note"
exit "$status"
