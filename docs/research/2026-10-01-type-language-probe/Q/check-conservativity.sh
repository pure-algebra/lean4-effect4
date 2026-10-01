#!/usr/bin/env bash
# The conservativity check of an alphabet append (DI-47, R3.8): seat Q, 2026-10-01.
#   check-conservativity.sh BASE [CAND] [--strict]   CAND a revision; omitted: the working tree
#   check-conservativity.sh --self-test              the red and green controls
# The clauses (C1 goldens, C2 alphabets, C3 verdicts, C4 policy, C5 record) are in
# bin/conservativity.py's docstring. Runs no producer and no build; reads committed files.
set -euo pipefail
exec python3 "$(cd "$(dirname "$0")" && pwd)/bin/conservativity.py" "$@"
