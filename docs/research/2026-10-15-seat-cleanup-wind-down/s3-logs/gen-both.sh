#!/bin/bash
# Scratch (seat CLEANUP, S3): regenerate the LCNF group, then the eff group, each timed.
set -u
cd /Users/pooks/Dev/lean4-effect4-cleanup
step() { echo "+ $*"; /usr/bin/time -p "$@"; echo "exit=$?"; }
step lake build OCaml5
step python3 scripts/generate.py --only lcnf
step python3 scripts/generate.py --only eff
