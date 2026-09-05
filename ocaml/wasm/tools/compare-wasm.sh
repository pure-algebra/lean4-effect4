#!/usr/bin/env bash
# Byte-compare the wasm corpus face against another face, program by program, with exactly
# the projection `ocaml/avatar/tools/compare-faces.sh` uses: the event rows only, because the
# header rows carry each run's own digests and pin.
#
#   wsl -e bash ocaml/wasm/tools/compare-wasm.sh <dirA> <dirB> [suffixA] [suffixB]
#
# e.g.  compare-wasm.sh ocaml/wasm/out/corpus/wasm-cps ocaml/avatar/out/corpus .tsv .ocaml.tsv
#
# Prints `MISSING <p>` / `DIFFER <p>` plus the first differing rows, then the summary line
# `faces: agree=N differ=N missing=N`. The program list is the avatar's `corpus/programs.txt`
# (158 `prog` lines), read from the repo, not from either directory.
set -uo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(CDPATH= cd -- "$here/../../.." && pwd)
a=${1:?dirA}; b=${2:?dirB}; sa=${3:-.tsv}; sb=${4:-.tsv}
progs=$(grep '^prog ' "$repo/ocaml/avatar/corpus/programs.txt" | awk '{print $2}' | tr -d '\r')
rows() { grep -E '^(op|answer|failed|decide|enter|leave|finalizer|done|frontier)\b' "$1" 2>/dev/null; }
agree=0; differ=0; missing=0
for p in $progs; do
  fa="$a/$p$sa"; fb="$b/$p$sb"
  if [ ! -f "$fa" ] || [ ! -f "$fb" ]; then missing=$((missing+1)); echo "MISSING $p"; continue; fi
  if diff -q <(rows "$fa") <(rows "$fb") > /dev/null; then agree=$((agree+1))
  else differ=$((differ+1)); echo "DIFFER $p"; diff <(rows "$fa") <(rows "$fb") | head -6; fi
done
echo "faces: agree=$agree differ=$differ missing=$missing"
