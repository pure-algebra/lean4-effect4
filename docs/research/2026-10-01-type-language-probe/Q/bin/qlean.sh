#!/usr/bin/env bash
# `lake env lean <args>` from the worktree, with the probe build directory on LEAN_PATH and one
# thread, so a generator's `importModules` and a probe's `import` see the probe modules.
set -euo pipefail
WT=/Users/pooks/Dev/lean4-effect4-probe-Q
QBUILD=${QBUILD:-/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/qbuild}
cd "$WT"
export LEAN_NUM_THREADS=1
LEAN_PATH="$QBUILD" exec lake env lean "$@"
