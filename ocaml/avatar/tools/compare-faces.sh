#!/usr/bin/env bash
# Byte-compare two corpus face directories, program by program (the `=== three OCaml hosts`
# block of `run-corpus.sh`, over any two directories of `<program>.tsv`).
#
#   compare-faces.sh <dirA> <dirB> [suffixA] [suffixB]
#
# Header rows (`generator`, `input`, ...) carry the run's own sha/pin values, so the
# comparison is over the event rows only, exactly as `compare.py` projects them.
set -uo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
a=${1:?dirA}; b=${2:?dirB}; sa=${3:-.tsv}; sb=${4:-.tsv}
progs=$(grep '^prog ' "$here/corpus/programs.txt" | awk '{print $2}' | tr -d '\r')
rows() { grep -E '^(op|answer|failed|decide|enter|leave|finalizer|done|frontier)\b' "$1" 2>/dev/null; }
agree=0; differ=0; missing=0
for p in $progs; do
  fa="$a/$p$sa"; fb="$b/$p$sb"
  if [ ! -f "$fa" ] || [ ! -f "$fb" ]; then missing=$((missing+1)); echo "MISSING $p"; continue; fi
  if diff -q <(rows "$fa") <(rows "$fb") > /dev/null; then agree=$((agree+1))
  else differ=$((differ+1)); echo "DIFFER $p"; diff <(rows "$fa") <(rows "$fb") | head -6; fi
done
echo "faces: agree=$agree differ=$differ missing=$missing"
