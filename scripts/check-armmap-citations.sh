#!/usr/bin/env bash
# Python-only arm-map refusal; no OCaml switch is needed.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
. "$repo_root/scripts/lib/stamp.sh"
cd "$repo_root"
key="$(stamp_key scripts/check-armmap-citations.sh scripts/check-armmap-citations.py ocaml/server/armmap-resolution.json \
  ocaml/server/tools/gen_armmap.py ocaml/server/dune src/Effect4/Machine ocaml/avatar/*.ml)"
if stamp_hit armmap-citations "$key"; then stamp_report armmap-citations "$key"; exit 0; fi
summary="$(python3 scripts/check-armmap-citations.py)"
printf '%s\n' "$summary"
stamp_write armmap-citations "$key" "$summary"
