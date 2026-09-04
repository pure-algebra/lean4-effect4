#!/usr/bin/env bash
# Route-1 spike entry, kept with its old interface: build everything (tools/build.sh:
# Bridge.o, the flag files, dune), then run the probe driver (the former e4.ml).
#
#   bash build-link.sh            # build, then run the probe with the default program
#   bash build-link.sh pTwo 50    # a program name and fuel for the probe
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
bash "$here/tools/build.sh"
echo "--- run"
exec "${E4_BUILD_DIR:-$here/_build}/default/e4_probe.exe" "${1:-pFork}" "${2:-100}"
