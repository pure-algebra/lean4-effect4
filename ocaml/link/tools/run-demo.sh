#!/usr/bin/env bash
# tools/run-demo.sh — build (no-op when current), then run the demo driver.
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
bash "$here/build.sh" >/dev/null
source "$here/lean-env.sh"
exec "${E4_BUILD_DIR:-$E4_LINK_DIR/_build}/default/e4_demo.exe" "$@"
