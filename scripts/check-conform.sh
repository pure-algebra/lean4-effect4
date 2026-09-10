#!/usr/bin/env bash
# Own the Lean lane, or join the matching enclosing generator/check owner.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake
lock=.lake/LANE.lock
owned=0
if mkdir "$lock" 2>/dev/null; then
  owned=1
  export EFFECT4_LANE_OWNER="conform-$$-$RANDOM"
  printf '%s\n' "$EFFECT4_LANE_OWNER" > "$lock/owner"
elif [[ -z "${EFFECT4_LANE_OWNER:-}" || ! -f "$lock/owner" ]] ||
     [[ "$(cat "$lock/owner")" != "$EFFECT4_LANE_OWNER" ]]; then
  echo 'FAIL conform: Lean lane is held by another run' >&2
  exit 2
fi
cleanup() {
  if [[ "$owned" = 1 ]]; then rm -f "$lock/owner"; rmdir "$lock"; fi
}
trap cleanup EXIT
export LEAN_NUM_THREADS=3
python3 scripts/check-conform.py "$@"
