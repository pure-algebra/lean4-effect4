#!/usr/bin/env bash
# Type receipts: the pinned, unpatched compiler emits declarations for the
# trace harness module, and the declaration line of every lowered program must
# be byte-equal to the line Lean renders (its A, E and R channels). Writes
# harness/trace/types/<program>.empty.receipt with the matched line and the
# digest of the emitted declaration file.
#
# ## Stamp (rule 9)
#
# What it reads: every TypeScript file and the tsconfig under `harness/trace/`,
# which it copies wholesale into a scratch project; `harness/trace/Generate.lean`
# and the Lake traces of its imports, which render the expected declaration
# lines; the pinned installation's identity; and the compiler it resolved,
# named by path rather than hashed -- `tsc.original` is 23 MB and its version is
# already pinned by `typescript/package.json`, which the identity covers. The
# receipts it writes are outputs, not inputs.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
. "$repo_root/scripts/lib/stamp.sh"
here="$repo_root/harness/trace"
for argument in "$@"; do
  case "$argument" in
    --force) export EFFECT4_FORCE=1 ;;
    *) echo "unknown argument $argument" >&2; exit 2 ;;
  esac
done
node_modules="$(cd "${EFFECT4_EFFECT_NODE_MODULES:-$HOME/Dev/foldlab/library/effects/node_modules}" && pwd)"
cd "$repo_root"
lake build Effect4 >/dev/null
tsc="$(find "$node_modules" -path '*/@typescript/typescript-*/lib/tsc.original' -type f -print -quit)"
[ -n "$tsc" ] || { echo "FAIL unpatched TypeScript compiler (tsc.original) not found" >&2; exit 1; }
inputs=(
  "$repo_root/scripts/check-lowering-types.sh"
  "$repo_root/scripts/lib/portable.sh"
  "$repo_root/scripts/lib/stamp.sh"
  "$here/Generate.lean"
  "$here/tsconfig.json"
  "$repo_root/lakefile.toml"
  "$repo_root/lake-manifest.json"
  "$repo_root/lean-toolchain"
)
for module in "$here"/*.ts; do inputs+=("$module"); done
while IFS= read -r input; do inputs+=("$input"); done < <(
  stamp_lean_traces "$here/Generate.lean"
  stamp_host_inputs
  stamp_fact tsc "$tsc"
)
key="$(stamp_key "${inputs[@]}")"
if stamp_hit lowering-types "$key"; then
  stamp_report lowering-types "$key"
  exit 0
fi
tmp="$(mktemp -d "${TMPDIR:-/tmp}/effect4-types.XXXXXX")"; trap 'rm -rf -- "$tmp"' EXIT
cp "$here"/*.ts "$here"/tsconfig.json "$tmp/" && ln -s "$node_modules" "$tmp/node_modules"
( cd "$tmp" && "$tsc" -p tsconfig.json --pretty false --noEmit false --declaration --emitDeclarationOnly --outDir "$tmp/out" ) \
  || { echo "FAIL declaration emit rejected the harness module" >&2; exit 1; }
emitted="$tmp/out/fixture.d.ts"
[ -f "$emitted" ] || { echo "FAIL no fixture.d.ts emitted" >&2; ls "$tmp/out" >&2; exit 1; }
digest="$(sha256 "$emitted")"
mkdir -p "$here/types"
# The generator runs once per list, up front: a refused or unknown command is a
# gate failure, never an empty loop.
lines="$tmp/types.tsv"; flow_lines="$tmp/flow-types.tsv"
# `lean_run` (scripts/lib/portable.sh) fails loudly with Lean's own diagnostic;
# an empty or exception-bearing list is still refused here, because Lean can
# print a usage error and exit zero.
lean_run "$here/Generate.lean" types > "$lines" \
  && ! grep -q '^uncaught exception' "$lines" && [ -s "$lines" ] \
  || { echo "FAIL Generate.lean types produced no declaration lines" >&2; cat "$lines" >&2; exit 1; }
lean_run "$here/Generate.lean" flow-types > "$flow_lines" \
  && ! grep -q '^uncaught exception' "$flow_lines" && [ -s "$flow_lines" ] \
  || { echo "FAIL Generate.lean flow-types produced no declaration lines" >&2; cat "$flow_lines" >&2; exit 1; }
status=0
while IFS=$'\t' read -r program expected; do
  if grep -Fxq -- "$expected" "$emitted"; then
    printf 'format\teffect4-type-receipt-v1\nprogram\t%s.empty\ntypescript\t%s\nfixture.d.ts\tsha256=%s\nline\t%s\n' \
      "$program" "$("$tsc" --version | sed 's/^Version //')" "$digest" "$expected" > "$here/types/$program.empty.receipt"
    echo "PASS type receipt $program: $expected"
  else
    echo "FAIL type receipt $program: expected line not emitted" >&2
    echo "  expected: $expected" >&2
    grep -F "export declare const $program" "$emitted" >&2 || echo "  (no declaration for $program)" >&2
    status=1
  fi
done < "$lines"
# --- the dispatch form -------------------------------------------------------
flow_emitted="$tmp/out/flow-fixture.d.ts"
[ -f "$flow_emitted" ] || { echo "FAIL no flow-fixture.d.ts emitted" >&2; ls "$tmp/out" >&2; exit 1; }
flow_digest="$(sha256 "$flow_emitted")"
mkdir -p "$here/types/flow"
while IFS=$'\t' read -r program tape expected; do
  if grep -Fxq -- "$expected" "$flow_emitted"; then
    printf 'format\teffect4-type-receipt-v1\nprogram\tflow/%s.%s\ntypescript\t%s\nflow-fixture.d.ts\tsha256=%s\nline\t%s\n' \
      "$program" "$tape" "$("$tsc" --version | sed 's/^Version //')" "$flow_digest" "$expected" > "$here/types/flow/$program.$tape.receipt"
    echo "PASS type receipt flow/$program.$tape: $expected"
  else
    echo "FAIL type receipt flow/$program.$tape: expected line not emitted" >&2
    echo "  expected: $expected" >&2
    grep -F "export declare const $program" "$flow_emitted" >&2 || echo "  (no declaration for $program)" >&2
    status=1
  fi
done < "$flow_lines"
# --- the structured form declares the same lines ------------------------------
structured_emitted="$tmp/out/structured-fixture.d.ts"
[ -f "$structured_emitted" ] || { echo "FAIL no structured-fixture.d.ts emitted" >&2; exit 1; }
while IFS=$'\t' read -r program tape expected; do
  if grep -Fxq -- "$expected" "$structured_emitted"; then echo "PASS type receipt structured/$program.$tape: same line"
  else echo "FAIL type receipt structured/$program.$tape: expected line not emitted" >&2; status=1; fi
done < "$flow_lines"
[ "$status" -eq 0 ] || exit "$status"
stamp_write lowering-types "$key" "$(printf \
  '%s straight-line and %s dispatch declaration lines matched, the structured form declaring the same' \
  "$(wc -l < "$lines" | tr -d ' ')" "$(wc -l < "$flow_lines" | tr -d ' ')")"
exit 0
