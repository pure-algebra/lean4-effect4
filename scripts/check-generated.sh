#!/usr/bin/env bash
# --stale checks provenance without Lean; default compares 25 fresh projections (the count
# lives in scripts/lib/check_generated.py and moved 24 -> 25 on 2026-09-09).
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$repo_root"
. scripts/lib/known-red.sh
known_red_load
if known_red_declared gate generated-stale; then
  exec python3 scripts/lib/check_generated.py --declared-reason "$(known_red_reason gate generated-stale)" "$@"
else
  exec python3 scripts/lib/check_generated.py "$@"
fi
