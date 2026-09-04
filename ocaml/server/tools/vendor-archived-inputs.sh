#!/usr/bin/env bash
# Re-extract the daemon's archived inputs from git.
#
# `generated/traces/` (the mask table and the 25 goldens of ref, deferred, scope and layer)
# and `harness/trace/*fixture*.ts` left main with the Flow route in 75002d7 ("Prod cleanup
# 1: archive the Flow route"); they live on branch `archive/flow-route`, at 606918e. The
# daemon's `masks`, `families` and `pins` answers are generated from them and its test
# client compares against them, so this script copies exactly those files, byte for byte,
# from that revision into server/generated/, and records which blob each came from in
# server/generated/archived-from.tsv.
#
#   tools/vendor-archived-inputs.sh          # from 606918e
#   tools/vendor-archived-inputs.sh <rev>    # from another revision that carries them
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
# <repo>/ocaml/server -> <repo>. The estate lived under `workshop/OCaml5/` until 2026-09-04.
repo=$(CDPATH= cd -- "$here/../.." && pwd)
rev=${1:-606918e}
out="$here/generated"
manifest="$out/archived-from.tsv"
mkdir -p "$out/traces" "$out/harness-trace"
printf 'revision\t%s\n' "$(git -C "$repo" rev-parse "$rev")" > "$manifest"

copy() { # <path in the revision> <destination>
  mkdir -p "$(dirname "$2")"
  git -C "$repo" show "$rev:$1" > "$2"
  printf '%s\t%s\t%s\n' "${2#"$here"/}" "$1" "$(git -C "$repo" rev-parse "$rev:$1")" >> "$manifest"
}

copy generated/traces/masks.tsv "$out/traces/masks.tsv"
for path in $(git -C "$repo" ls-tree -r --name-only "$rev" -- \
    generated/traces/ref generated/traces/deferred generated/traces/scope generated/traces/layer); do
  copy "$path" "$out/traces/${path#generated/traces/}"
done
for name in fibers-fixture.stub.ts ref-fixture.ts deferred-fixture.ts scope-fixture.ts layer-fixture.ts; do
  copy "harness/trace/$name" "$out/harness-trace/$name"
done
echo "vendored $(($(wc -l < "$manifest") - 1)) files from $rev into $out"
