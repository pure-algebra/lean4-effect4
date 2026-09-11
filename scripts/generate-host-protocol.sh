#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Effect4.Api.HostSession
lake env lean -M4096 --run tools/Tools/HostProtocol.lean harness/truth/session
