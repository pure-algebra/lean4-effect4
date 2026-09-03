#!/usr/bin/env bash
# Hermetic drift gate: regenerate the Lean-expected traces and compare them
# byte for byte with generated/traces/. Needs no host.
#
# ## Stamp (rule 9)
#
# What this gate reads: its own bytes and those of the generator it calls; the
# Lean driver `harness/trace/Generate.lean`, both for `all` and for the `oracle`
# command; the Lake trace of every module that driver imports, which stands for
# the whole olean closure beneath it; every committed projection under
# `generated/traces/`, because that is what the regeneration is compared with;
# and the Lake configuration, manifest and toolchain, since the generator prints
# the effects revision into every provenance block. The key is taken after
# `lake build Effect4`, so the traces it hashes are current.
#
# `--dry-run <dir>` compares against a candidate rather than the committed
# projections, so it neither consults nor writes a stamp.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
. "$repo_root/scripts/lib/stamp.sh"
# --dry-run <dir> compares the regeneration with <dir> instead of the committed
# projections; it exists for the mutation self-test and closes nothing.
committed_dir="$repo_root/generated/traces"; note=""; stamped=1
while [ $# -gt 0 ]; do
  case "$1" in
    --dry-run) committed_dir="$2"; note=" (dry run, closes nothing)"; stamped=0; shift 2 ;;
    --force) export EFFECT4_FORCE=1; shift ;;
    *) echo "unknown argument $1" >&2; exit 2 ;;
  esac
done
if [ "$stamped" -eq 1 ]; then
  ( cd "$repo_root" && lake build Effect4 >/dev/null )
  inputs=(
    "$repo_root/scripts/check-trace-goldens.sh"
    "$repo_root/scripts/generate-trace-goldens.sh"
    "$repo_root/scripts/lib/portable.sh"
    "$repo_root/scripts/lib/stamp.sh"
    "$repo_root/harness/trace/Generate.lean"
    "$committed_dir"
    "$repo_root/lakefile.toml"
    "$repo_root/lake-manifest.json"
    "$repo_root/lean-toolchain"
  )
  while IFS= read -r trace; do inputs+=("$trace"); done \
    < <(stamp_lean_traces "$repo_root/harness/trace/Generate.lean")
  key="$(stamp_key "${inputs[@]}")"
  if stamp_hit trace-goldens "$key"; then
    stamp_report trace-goldens "$key"
    exit 0
  fi
fi
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
[ "$status" -eq 0 ] || exit "$status"
summary="generated/traces is current ($(find "$tmp" -name '*.tsv' | wc -l | tr -d ' ') files)"
if [ "$stamped" -eq 1 ]; then stamp_write trace-goldens "$key" "$summary"; fi
echo "PASS $summary$note"
