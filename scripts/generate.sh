#!/usr/bin/env bash
# Generate committed projections in dependency order. No generation verdict is cached.
# Usage: scripts/generate.sh [--all | --only derived|eff|wire|cas|ts|readme|lcnf]
# --all and no argument are the same named order (DI-33): derived, eff, wire, cas, ts, readme.
# `readme` is the ingest tables (`bun ts/eff/ingest/render-readme.ts`), a host producer that
# reads three files `ts` just wrote. `lcnf` is not in the order; it is requested by name.
# The Truth family is not here either: it is a host-lane family with its own two commands
# (docs/GENERATED.md), because Lean reads the committed tapes that rc.112 re-records.
# --output-dir DIR is the drift check's temporary destination; canonical files stay put.
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$repo_root"
command -v timeout >/dev/null || { echo 'FAIL generate: timeout is required' >&2; exit 1; }
export LEAN_NUM_THREADS=3
lock="$repo_root/.lake/LANE.lock"
mkdir -p "$repo_root/.lake"
owned=0
if mkdir "$lock" 2>/dev/null; then
  owned=1
  export EFFECT4_LANE_OWNER="generated-$$-$RANDOM"
  printf '%s\n' "$EFFECT4_LANE_OWNER" > "$lock/owner"
elif [[ -z "${EFFECT4_LANE_OWNER:-}" || ! -f "$lock/owner" ]] ||
     [[ "$(cat "$lock/owner")" != "$EFFECT4_LANE_OWNER" ]]; then
  echo 'FAIL generate: Lean lane is held by another run' >&2
  exit 1
fi
cleanup() {
  if [[ "$owned" = 1 ]]; then rm -f "$lock/owner"; rmdir "$lock"; fi
}
trap cleanup EXIT
python3 scripts/lib/generate.py "$@"
