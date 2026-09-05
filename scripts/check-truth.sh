#!/usr/bin/env bash
# Host gate: bun and effect@4.0.0-rc.112 (EFFECT4_EFFECT_NODE_MODULES).
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
exec python3 "$repo_root/scripts/check-truth.py"
