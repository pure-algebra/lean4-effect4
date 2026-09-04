#!/bin/sh
# Fuzz the OCaml 5 reference machine against the three hosts of ruling 7.
#
# Spike P5 of docs/research/2026-09-03-ocaml5-deep-plan.md §6. `OCaml5.Render` turns an
# `OCaml5.Term` into an OCaml 5 compilation unit and `OCaml5.Fuzz` generates the terms; this
# script compiles each generated program as bytecode, as native code and through js_of_ocaml,
# runs all three, and compares FOUR row lists: the three hosts and `Machine.rows`.
#
#   tools/fuzz.sh witnesses              render the 13 witnesses and check them on all hosts
#   tools/fuzz.sh surface                render the A0 shape probe (OCaml5.Ml) and check it
#   tools/fuzz.sh run FIRST COUNT SIZE   generate seeds FIRST… and check COUNT of them
#   tools/fuzz.sh shrink SEED SIZE       minimise the disagreement of one seed
#
# Verdicts, one per program:
#   AGREE        all four row lists equal
#   LEAN         the three hosts agree with each other and disagree with the Lean machine
#   HOSTS        the hosts disagree with each other (a ruling-3 finding)
#   REFUSED      a host refused to compile the rendered source
#
# Build products go under $P5_BUILD (default: the session scratchpad), never into the
# repository and never into the opam switches. Environment: OCAMLC, OCAMLOPT, OCAMLRUN,
# JSOO, NODE, P5_BUILD, P5_JOBS.

set -u

REPO=$(cd "$(dirname "$0")/../../.." && pwd)
OCAMLC=${OCAMLC:-/Users/pooks/.opam/default/bin/ocamlc}
OCAMLOPT=${OCAMLOPT:-/Users/pooks/.opam/default/bin/ocamlopt}
OCAMLRUN=${OCAMLRUN:-/Users/pooks/.opam/default/bin/ocamlrun}
JSOO=${JSOO:-/Users/pooks/Dev/effect4_of_ocaml/_build/toolchains/ocaml5-jsoo-5.7.1/_build/default/vendor/js_of_ocaml-compiler.5.7.1/compiler/bin-js_of_ocaml/js_of_ocaml.exe}
NODE=${NODE:-node}
P5_BUILD=${P5_BUILD:-/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/d87ba830-2e63-4750-815f-2679b36f870a/scratchpad/p5}
P5_JOBS=${P5_JOBS:-8}
LEANRUN="lake env lean --run workshop/OCaml5/Fuzz.lean"

# ---------------------------------------------------------------------------
# check ONE rendered program: $1 is the .ml, its .rows sibling holds Machine.rows.
# Prints one line: "<verdict> <name>" and leaves the four row lists in the work dir.
# ---------------------------------------------------------------------------
check_one() {
  src=$1
  name=$(basename "$src" .ml)
  base=$(dirname "$src")
  dir="$P5_BUILD/work/$name"
  rm -rf "$dir"; mkdir -p "$dir" || return 1
  cp "$src" "$dir/w.ml"
  cp "$base/$name.rows" "$dir/lean.rows"

  ( cd "$dir" && "$OCAMLC" -w -a -o w.byte w.ml ) >"$dir/byte.build" 2>&1 \
    || { echo "REFUSED-byte $name"; return 0; }
  ( cd "$dir" && "$OCAMLRUN" w.byte ) >"$dir/byte.rows" 2>"$dir/byte.err"

  ( cd "$dir" && "$OCAMLOPT" -w -a -o w.native w.ml ) >"$dir/native.build" 2>&1 \
    || { echo "REFUSED-native $name"; return 0; }
  ( cd "$dir" && ./w.native ) >"$dir/native.rows" 2>"$dir/native.err"

  ( cd "$dir" && "$JSOO" compile --enable effects --target-env=nodejs w.byte -o w.js ) \
    >"$dir/jsoo.build" 2>&1 \
    || { echo "REFUSED-jsoo $name"; return 0; }
  ( cd "$dir" && "$NODE" w.js ) >"$dir/jsoo.rows" 2>"$dir/jsoo.err"

  if cmp -s "$dir/byte.rows" "$dir/native.rows" && cmp -s "$dir/byte.rows" "$dir/jsoo.rows"; then
    if cmp -s "$dir/byte.rows" "$dir/lean.rows"; then
      echo "AGREE $name"
    else
      echo "LEAN $name"
    fi
  else
    echo "HOSTS $name"
  fi
}

summarise() {
  # $1 = results file
  total=$(wc -l < "$1" | tr -d ' ')
  echo "programs checked: $total"
  awk '{print $1}' "$1" | sort | uniq -c | sed 's/^/  /'
  bad=$(grep -c -v '^AGREE ' "$1")
  echo "disagreements: $bad"
  if [ "$bad" -gt 0 ]; then
    grep -v '^AGREE ' "$1" | sed 's/^/  /'
  fi
}

case "${1:-}" in
  _one)
    check_one "$2"
    ;;

  witnesses)
    wdir="$P5_BUILD/witnesses"
    rm -rf "$wdir"; mkdir -p "$wdir"
    ( cd "$REPO" && $LEANRUN witnesses "$wdir" ) || exit 1
    res="$P5_BUILD/witnesses.results"; : > "$res"
    for f in "$wdir"/*.ml; do
      n=$(basename "$f" .ml)
      # `Machine.rows` must already equal the recorded bytecode rows of `OCaml5.Witnesses`.
      if ! cmp -s "$wdir/$n.rows" "$wdir/$n.byte-expected"; then
        echo "MACHINE-VS-RECORDED $n" >> "$res"; continue
      fi
      check_one "$f" >> "$res"
    done
    summarise "$res"
    ;;

  surface)
    sdir="$P5_BUILD/surface"
    rm -rf "$sdir"; mkdir -p "$sdir"
    ( cd "$REPO" && $LEANRUN surface "$sdir" ) || exit 1
    check_one "$sdir/surface.ml"
    ;;

  run)
    first=${2:?FIRST}; count=${3:?COUNT}; size=${4:?SIZE}
    gen="$P5_BUILD/gen-$first-$count-$size"
    rm -rf "$gen"; mkdir -p "$gen"
    ( cd "$REPO" && $LEANRUN gen "$gen" "$first" "$count" "$size" ) || exit 1
    res="$P5_BUILD/results-$first-$count-$size.txt"
    ls "$gen"/*.ml | xargs -P "$P5_JOBS" -n 1 "$0" _one > "$res"
    sort -o "$res" "$res"
    summarise "$res"
    ;;

  shrink)
    seed=${2:?SEED}; size=${3:?SIZE}
    shr="$P5_BUILD/shrink-$seed"
    rm -rf "$shr"; mkdir -p "$shr"
    ( cd "$REPO" && $LEANRUN one "$shr" cur "$seed" "$size" ) >/dev/null || exit 1
    want=$(check_one "$shr/cur.ml" | awk '{print $1}')
    echo "seed $seed starts as $want"
    [ "$want" = "AGREE" ] && { echo "nothing to shrink"; exit 0; }
    path=""
    while : ; do
      cdir="$shr/c"; rm -rf "$cdir"; mkdir -p "$cdir"
      # shellcheck disable=SC2086
      ( cd "$REPO" && $LEANRUN cands "$cdir" "$seed" "$size" $path ) >/dev/null || break
      [ -s "$cdir/cands.txt" ] || break
      picked=""
      for i in $(cat "$cdir/cands.txt"); do
        v=$(check_one "$cdir/c$i.ml" | awk '{print $1}')
        if [ "$v" = "$want" ]; then picked=$i; break; fi
      done
      [ -z "$picked" ] && break
      path="$path $picked"
      echo "  step $picked (path:$path)"
    done
    # shellcheck disable=SC2086
    ( cd "$REPO" && $LEANRUN one "$shr" min "$seed" "$size" $path )
    echo "minimised: $shr/min.ml"
    check_one "$shr/min.ml"
    cp "$P5_BUILD/work/min/byte.rows" "$shr/min.byte.rows" 2>/dev/null
    cp "$P5_BUILD/work/min/native.rows" "$shr/min.native.rows" 2>/dev/null
    cp "$P5_BUILD/work/min/jsoo.rows" "$shr/min.jsoo.rows" 2>/dev/null
    echo "path:$path"
    ;;

  *)
    sed -n '2,30p' "$0"
    exit 2
    ;;
esac
