#!/usr/bin/env bash
# The trace harness: hermetic golden drift, then the host comparison.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"$repo_root/scripts/check-trace-goldens.sh"
"$repo_root/scripts/check-trace-host.sh" "$@"
