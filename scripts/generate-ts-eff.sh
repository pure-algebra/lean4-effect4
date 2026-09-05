#!/usr/bin/env bash
# Regenerate the TypeScript estate's generated files from the Lean environment:
#
#   ts/eff/eff.gen.ts      the families of the Eff IR as Effect Schema nodes, with their types
#   ts/eff/json.gen.ts     one JSON writer per family (the bytes Lean and OCaml write)
#   ts/eff/profile.gen.ts  the image profile: address, reserved heads, and one entry per
#                          native operation (the operation and its row as nodes), stamped
#
#   ./scripts/generate-ts-eff.sh [<dir>]      default ts/eff
#
# A generator, not a gate (scripts/lib/stamp.sh, "Generators are not stamped"): it builds
# `Tools.TsGen`, the one Lean module it runs, and writes. The byte-for-byte drift gate over the
# written files is scripts/check-ts-eff.sh, stamped, in the sweep. Nothing here is typed by
# hand: the families, constructors, field names and carriers are read off the environment
# (`OCaml5.Eff.World`), the heads are `Effect4.Program.reserved`, the rows `NativeOp.row`.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
. "$repo_root/scripts/lib/portable.sh"

out="${1:-$repo_root/ts/eff}"
cd "$repo_root"

build_log="$(mktemp "${TMPDIR:-/tmp}/effect4-ts-eff-build.XXXXXX")"
if ! lake build Tools.TsGen >"$build_log" 2>&1; then
  printf 'FAIL generate-ts-eff: lake build Tools.TsGen failed\n' >&2
  cat "$build_log" >&2
  rm -f "$build_log"
  exit 1
fi
rm -f "$build_log"

lean_run src/Tools/TsGen.lean "$out"
