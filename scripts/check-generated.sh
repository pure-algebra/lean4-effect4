#!/usr/bin/env bash
# --stale checks provenance without Lean; default compares the complete mapped output set
# of the selected producers, including CAS bytes and the engine structural mirror.
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
