#!/usr/bin/env bash
# Existence of live repository citation targets; line numbers are not resolved.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
exec python3 "$repo_root/scripts/check-source-citations.py" "$@"
