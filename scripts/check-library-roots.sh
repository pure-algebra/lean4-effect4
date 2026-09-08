#!/usr/bin/env bash
# A fresh audit sees new orphan source files even when Lake's roots are cached.
# The compiled import graph and the source inventory are checked by AxiomGate.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
log="$(mktemp "${TMPDIR:-/tmp}/effect4-library-roots.XXXXXX")"
trap 'rm -f -- "$log"' EXIT
if ! lake build Test >"$log" 2>&1; then
  cat "$log" >&2
  exit 1
fi
lake env lean "$repo_root/Test/All.lean"
echo 'PASS library-roots: fresh module, root-closure and axiom audit'
