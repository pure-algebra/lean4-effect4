#!/usr/bin/env bash
# The former serial sweep. Since 2026-09-13 the checks are Makefile targets in tiers
# (`make help`): `make check` after every change, `make check-host` per slice,
# `make check-full` for everything. This wrapper keeps the old entry point and maps its
# flags onto those tiers; it will be removed once nothing calls it.
#
#   scripts/sweep.sh               make check-full
#   scripts/sweep.sh --hermetic    make check
#   scripts/sweep.sh --keep-going  make -k check-full
#   scripts/sweep.sh --list        make help
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$repo_root"
target=check-full
flags=()
for argument in "$@"; do
  case "$argument" in
    --hermetic)   target=check ;;
    --ocaml)      target=check-ocaml ;;
    --keep-going) flags+=(-k) ;;
    --list)       exec make help ;;
    *) echo "sweep: unknown flag $argument (see make help)" >&2; exit 2 ;;
  esac
done
echo "sweep: this runner is retired; running: make ${flags[*]:-} $target" >&2
exec make ${flags[@]+"${flags[@]}"} "$target"
