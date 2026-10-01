#!/bin/sh
# Probe U's one compiler entry (one process at a time; LEAN_NUM_THREADS=1; warnings are errors).
#   run-lean.sh check <file.lean>             compile a probe that imports the tree (and ProbeU.*)
#   run-lean.sh olean <ProbeU/Module.lean>    compile a probe module to U/olean/ProbeU/Module.olean
#   run-lean.sh olean-gen <file>              the same for a generated module under U/generated
# The probe modules live under U/probes, the generated ones under U/generated (the roots for
# module names); their oleans under U/olean.
set -eu
U="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$U/../../../.." && pwd)"
cd "$ROOT"
mode="$1"; file="$2"
case "$mode" in
  check)
    LEAN_NUM_THREADS=1 lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$U/olean\" lean -DwarningAsError=true \"$file\"" ;;
  olean)
    rel="${file#$U/probes/}"
    out="$U/olean/${rel%.lean}.olean"
    mkdir -p "$(dirname "$out")"
    LEAN_NUM_THREADS=1 lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$U/olean\" lean -DwarningAsError=true -R \"$U/probes\" -o \"$out\" \"$file\"" ;;
  olean-gen)
    rel="${file#$U/generated/}"
    out="$U/olean/${rel%.lean}.olean"
    mkdir -p "$(dirname "$out")"
    LEAN_NUM_THREADS=1 lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$U/olean\" lean -DwarningAsError=true -R \"$U/generated\" -o \"$out\" \"$file\"" ;;
  *) echo "usage: run-lean.sh check|olean|olean-gen <file>" >&2; exit 2 ;;
esac
