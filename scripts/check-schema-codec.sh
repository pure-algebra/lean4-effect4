#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
export LEAN_NUM_THREADS=3
lock=.lake/LANE.lock
acquired=0
if mkdir "$lock" 2>/dev/null; then
  acquired=1
  export EFFECT4_LANE_OWNER="schema-codec-$$"
  printf '%s\n' "$EFFECT4_LANE_OWNER" > "$lock/owner"
elif [[ -z "${EFFECT4_LANE_OWNER:-}" || ! -f "$lock/owner" ]] ||
    [[ "$(cat "$lock/owner")" != "$EFFECT4_LANE_OWNER" ]]; then
  echo 'schema-codec: another session holds the Lean lane' >&2
  exit 1
fi
temporary_dir="$(mktemp -d)"
cleanup() {
  rm -rf "$temporary_dir"
  if [[ "$acquired" == 1 ]]; then rm -rf "$lock"; fi
}
trap cleanup EXIT
lake build Test.Codegen.SchemaGenerationContract > "$temporary_dir/build.log" 2>&1 || {
  cat "$temporary_dir/build.log" >&2
  exit 1
}
lake env lean -M4096 --run harness/truth/schema-codec/Emit.lean "$temporary_dir/values.ts"
node harness/truth/node_modules/typescript/bin/tsc --project harness/truth/schema-codec/tsconfig.json
bun harness/truth/schema-codec/check.ts "$temporary_dir/values.ts"
