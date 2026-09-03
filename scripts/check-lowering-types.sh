#!/usr/bin/env bash
# Type receipts: the pinned, unpatched compiler emits declarations for the
# trace harness module, and the declaration line of every lowered program must
# be byte-equal to the line Lean renders (its A, E and R channels). Writes
# harness/trace/types/<program>.empty.receipt with the matched line and the
# digest of the emitted declaration file.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
here="$repo_root/harness/trace"
node_modules="$(cd "${EFFECT4_EFFECT_NODE_MODULES:-$HOME/Dev/foldlab/library/effects/node_modules}" && pwd)"
cd "$repo_root"
lake build Effect4 >/dev/null
tsc="$(find "$node_modules" -path '*/@typescript/typescript-*/lib/tsc.original' -type f -print -quit)"
[ -n "$tsc" ] || { echo "FAIL unpatched TypeScript compiler (tsc.original) not found" >&2; exit 1; }
tmp="$(mktemp -d "${TMPDIR:-/tmp}/effect4-types.XXXXXX")"; trap 'rm -rf -- "$tmp"' EXIT
cp "$here"/*.ts "$here"/tsconfig.json "$tmp/" && ln -s "$node_modules" "$tmp/node_modules"
( cd "$tmp" && "$tsc" -p tsconfig.json --pretty false --noEmit false --declaration --emitDeclarationOnly --outDir "$tmp/out" ) \
  || { echo "FAIL declaration emit rejected the harness module" >&2; exit 1; }
emitted="$tmp/out/fixture.d.ts"
[ -f "$emitted" ] || { echo "FAIL no fixture.d.ts emitted" >&2; ls "$tmp/out" >&2; exit 1; }
digest="$(shasum -a 256 "$emitted" | cut -d' ' -f1)"
mkdir -p "$here/types"
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
done < <(lake env lean --run "$here/Generate.lean" types | grep -v '^warning: manifest out of date')
# --- the dispatch form -------------------------------------------------------
flow_emitted="$tmp/out/flow-fixture.d.ts"
[ -f "$flow_emitted" ] || { echo "FAIL no flow-fixture.d.ts emitted" >&2; ls "$tmp/out" >&2; exit 1; }
flow_digest="$(shasum -a 256 "$flow_emitted" | cut -d' ' -f1)"
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
done < <(lake env lean --run "$here/Generate.lean" flow-types | grep -v '^warning: manifest out of date')
exit "$status"
