#!/usr/bin/env bash
# The conservativity check of an alphabet append (DI-47, R3.8; decisions row 172): probe Q's
# check, landed by seat W2 with the revision repair of row 172's amendment.
#   scripts/check-conservativity.sh BASE [CAND] [--strict]   CAND a revision; omitted: the working tree
#   scripts/check-conservativity.sh --self-test              the controls
# The clauses (C1 goldens, C2 alphabets, C3 verdicts, C4 policy, C5 record) are in
# scripts/lib/conservativity.py's docstring. Runs no producer and no build; reads committed files,
# so an append's producers and `make corpus` run first. Every revision is resolved to a commit
# before anything is read; an unresolved one or a failed git command is a refusal (exit 1).
set -euo pipefail
exec python3 "$(cd "$(dirname "$0")" && pwd)/lib/conservativity.py" "$@"
