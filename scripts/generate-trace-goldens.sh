#!/usr/bin/env bash
# Writes the Lean-expected traces of the harness families and the registered
# mask table into generated/traces/ (or the directory given as $1). Each file
# carries provenance rows (generator, regenerate command, inputs with digests,
# the effects pin) followed by the rows Generate.lean prints.
#
# This script owns the provenance prologue and nothing else. Which families
# exist, which projections each has, and which subdirectory keeps a family out
# of another family's glob are all facts of `harness/trace/Generate.lean`, and
# its `all` command writes every projection in one Lean process. The shell used
# to spawn one full elaboration per golden -- about seventy of them, 86 s to
# 220 s -- for outputs that are byte-identical to the single run (survey
# finding H11).
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
out="${1:-$repo_root/generated/traces}"
mkdir -p "$out"
cd "$repo_root"
lake build Effect4 >/dev/null
effects_rev="$(python3 -c "import json;m=json.load(open('lake-manifest.json'));print(next(p['rev'] for p in m['packages'] if p['name']=='effects'))")"
# An abbreviated revision is not a durable identifier, and the corpus once
# carried two widths at the same time (survey finding H10). Refuse before a
# byte is printed.
[[ "$effects_rev" =~ ^[0-9a-f]{40}$ ]] || {
  echo "FAIL lake-manifest.json gives the effects rev as '$effects_rev'; a golden pin must be 40 hex characters" >&2
  echo "  put the full sha in lakefile.toml and re-resolve the manifest" >&2
  exit 1
}
provenance="$(mktemp "${TMPDIR:-/tmp}/effect4-provenance.XXXXXX")"
trap 'rm -f -- "$provenance"' EXIT
{
  printf 'format\teffect4-trace-golden-v1\n'
  printf 'generator\tscripts/generate-trace-goldens.sh\tsha256=%s\n' "$(sha256 scripts/generate-trace-goldens.sh)"
  printf 'regenerate\t./scripts/generate-trace-goldens.sh\n'
  printf 'input\tharness/trace/Generate.lean\tsha256=%s\n' "$(sha256 harness/trace/Generate.lean)"
  printf 'input\tEffect4/Meta/Derive.lean\tsha256=%s\n' "$(sha256 Effect4/Meta/Derive.lean)"
  printf 'input\tEffect4/Target/TypeScript/Trace.lean\tsha256=%s\n' "$(sha256 Effect4/Target/TypeScript/Trace.lean)"
  printf 'pin\teffects\t%s\n' "$effects_rev"
} > "$provenance"
lean_run harness/trace/Generate.lean all "$out" "$provenance"
echo "PASS wrote $(find "$out" -name '*.tsv' | wc -l | tr -d ' ') trace projections to $out"
