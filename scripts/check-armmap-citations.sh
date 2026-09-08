#!/usr/bin/env bash
# Python-only arm-map refusal; no OCaml switch is needed.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
. "$repo_root/scripts/lib/stamp.sh"
. "$repo_root/scripts/lib/known-red.sh"
cd "$repo_root"
gate=armmap-citations
known_red_load
key="$(stamp_key scripts/check-armmap-citations.sh scripts/check-armmap-citations.py \
  scripts/lib/known-red.sh Test/fixtures/trust-gate/known-red.txt ocaml/server/armmap-resolution.json \
  ocaml/server/tools/gen_armmap.py ocaml/server/dune \
  src/Effect4/Machine src/Effect4/Laws/Machine ocaml/avatar/*.ml)"
if ! known_red_declared gate "$gate" && stamp_hit "$gate" "$key"; then
  stamp_report "$gate" "$key"; exit 0
fi
# Exit 3 identifies resolution drift. A broken checker or missing input must
# still refuse even when the existing resolution debt is declared.
status=0
summary="$(python3 scripts/check-armmap-citations.py)" || status=$?
printf '%s\n' "$summary"
case "$status" in
  0) observed=pass ;;
  3) observed=fail ;;
  *) printf 'FAIL %s: checker failed (exit %s)\n' "$gate" "$status" >&2; exit "$status" ;;
esac
verdict="$(known_red_verdict gate "$gate" "$observed")" || {
  printf 'FAIL %s: %s\n' "$gate" "$verdict" >&2
  exit 1
}
if known_red_declared gate "$gate"; then
  printf 'PASS %s: %s -- %s\n' "$gate" "$verdict" "$(known_red_reason gate "$gate")"
  exit 0 # A declared red result is always executed, never stamped.
fi
stamp_write "$gate" "$key" "$summary"
