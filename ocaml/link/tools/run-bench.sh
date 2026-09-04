#!/usr/bin/env bash
# tools/run-bench.sh — build (no-op when current), then run the bench driver.
#   bash tools/run-bench.sh [machines=200] [reps=3] [single-iters=20000]
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
bash "$here/build.sh" >/dev/null
source "$here/lean-env.sh"
exec "${E4_BUILD_DIR:-$E4_LINK_DIR/_build}/default/e4_bench.exe" "$@"
