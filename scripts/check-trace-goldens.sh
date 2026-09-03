#!/usr/bin/env bash
# Hermetic drift gate: regenerate the Lean-expected traces and compare them
# byte for byte with generated/traces/. Needs no host.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
# --dry-run <dir> compares the regeneration with <dir> instead of the committed
# projections; it exists for the mutation self-test and closes nothing.
committed_dir="$repo_root/generated/traces"; note=""
if [ "${1:-}" = "--dry-run" ]; then committed_dir="$2"; note=" (dry run, closes nothing)"; fi
tmp="$(mktemp -d "${TMPDIR:-/tmp}/effect4-traces.XXXXXX")"
trap 'rm -rf -- "$tmp"' EXIT
# One Lean process writes the whole corpus (`Generate.lean all`), so this gate
# costs one elaboration rather than one per golden (survey finding H11).
"$repo_root/scripts/generate-trace-goldens.sh" "$tmp" >/dev/null
status=0
while IFS= read -r candidate; do
  name="${candidate#"$tmp"/}"
  if ! cmp -s "$candidate" "$committed_dir/$name"; then
    echo "FAIL stale generated trace projection: $name" >&2
    diff -u "$committed_dir/$name" "$candidate" 2>/dev/null | head -20 >&2 || true
    status=1
  fi
done < <(find "$tmp" -name '*.tsv' | LC_ALL=C sort)
while IFS= read -r committed; do
  name="${committed#"$committed_dir"/}"
  [ -f "$tmp/$name" ] || { echo "FAIL orphan trace projection: $name" >&2; status=1; }
done < <(find "$committed_dir" -name '*.tsv' | LC_ALL=C sort)
# The internal oracle: the Flow runner and the traced service agree under m2.
if ! ( cd "$repo_root" && lean_run harness/trace/Generate.lean oracle ); then
  echo "FAIL flow oracle: the Flow runner and the traced service disagree" >&2
  status=1
fi
[ "$status" -eq 0 ] && echo "PASS generated/traces is current ($(find "$tmp" -name '*.tsv' | wc -l | tr -d ' ') files)$note"
exit "$status"
