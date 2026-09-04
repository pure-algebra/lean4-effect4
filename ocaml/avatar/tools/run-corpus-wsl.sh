#!/usr/bin/env bash
# The corpus on the two WSL faces of the dune build (`run-corpus.sh` adapted to this machine:
# no Mac scratch dir, no `avatar.byte`/`avatar.native` names -- dune's `avatar_main.bc` and
# `avatar_main.exe`; the js_of_ocaml face runs under the Windows `node`, see
# `run-corpus-jsoo.ps1`).
#
#   run-corpus-wsl.sh <outdir>
#
# Writes <outdir>/native/<program>.tsv and <outdir>/byte/<program>.tsv, one per `prog` line of
# `corpus/programs.txt`, and prints the counts. Give an <outdir> under /mnt/c: WSL2's `/tmp`
# is a tmpfs that is gone once the VM idles out between invocations.
#
# The binaries: the workspace build (`dune build avatar` from `ocaml/`, into
# `ocaml/_build/default/avatar/`) is preferred; the project-local `--root .` build
# (`avatar/_build/default/`) is the fallback, and `AVATAR_BIN` overrides both.
set -uo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out=${1:?usage: run-corpus-wsl.sh <outdir>}
bin=${AVATAR_BIN:-}
if [ -z "$bin" ]; then
  if   [ -x "$here/../_build/default/avatar/avatar_main.exe" ]; then bin="$here/../_build/default/avatar"
  elif [ -x "$here/_build/default/avatar_main.exe" ];           then bin="$here/_build/default"
  else echo "no avatar_main.exe: build with 'dune build avatar' from ocaml/" >&2; exit 1; fi
fi
echo "binaries: $bin"
mkdir -p "$out/native" "$out/byte"
progs=$(grep '^prog ' "$here/corpus/programs.txt" | awk '{print $2}' | tr -d '\r')
native_ok=0; native_bad=0; byte_ok=0; byte_bad=0
for p in $progs; do
  if EFFECT4_FAMILY=corpus EFFECT4_PROGRAM="$p" timeout 20 "$bin/avatar_main.exe" \
       > "$out/native/$p.tsv" 2>"$out/native/$p.err"; then native_ok=$((native_ok+1))
  else native_bad=$((native_bad+1)); echo "NATIVE-FAIL $p: $(head -1 "$out/native/$p.err")"; fi
  if EFFECT4_FAMILY=corpus EFFECT4_PROGRAM="$p" timeout 20 ocamlrun "$bin/avatar_main.bc" \
       > "$out/byte/$p.tsv" 2>"$out/byte/$p.err"; then byte_ok=$((byte_ok+1))
  else byte_bad=$((byte_bad+1)); echo "BYTE-FAIL $p: $(head -1 "$out/byte/$p.err")"; fi
done
echo "native ok=$native_ok bad=$native_bad ; byte ok=$byte_ok bad=$byte_bad"
agree=0; disagree=0
for p in $progs; do
  if cmp -s "$out/native/$p.tsv" "$out/byte/$p.tsv"; then agree=$((agree+1))
  else disagree=$((disagree+1)); echo "native/byte DISAGREE $p"; fi
done
echo "native = byte on $agree programs, differ on $disagree"
