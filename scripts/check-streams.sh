#!/usr/bin/env bash
# Pinned host examples and controls. No Lean compiler is required by this lane.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
python3 scripts/generate-effect-stream-census.py
python3 scripts/generate-effect-stream-census.py --check
bun ts/eff/node_modules/typescript/bin/tsc --pretty false -p harness/streams/tsconfig.json
bun harness/streams/typecheck-boundaries.ts
bun test harness/streams/instrument.test.ts harness/streams/boundary.test.ts
if [ "${EFFECT4_FORCE:-0}" = 1 ]; then
  bun harness/streams/run.ts --force "$@"
else
  bun harness/streams/run.ts "$@"
fi
