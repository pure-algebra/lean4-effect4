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
#   tools/fuzz.sh avatar                 render the avatar carriers, compile them, diff vs A0
#   tools/fuzz.sh tapes SEED COUNT LEN   generate RunDecision tapes and type-check them
#   tools/fuzz.sh corpus [FIRST COUNT]   generate the round-four program corpus under fuzz/corpus
#   tools/fuzz.sh corpus-smoke [SAMPLE]  compile the corpus: ocamlc for the .ml, tsc for the .ts
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
NODE_MODULES=${EFFECT4_EFFECT_NODE_MODULES:-$HOME/Dev/foldlab/library/effects/node_modules}
TSC=${TSC:-$NODE_MODULES/.bin/tsc}
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

  avatar)
    adir="$P5_BUILD/avatar"
    rm -rf "$adir"; mkdir -p "$adir"
    ( cd "$REPO" && $LEANRUN avatar "$adir" ) || exit 1
    # 1. it compiles, on all three hosts
    ( cd "$adir" && "$OCAMLC" -w -a -c avatar_check.ml ) >"$adir/byte.build" 2>&1 \
      && echo "ocamlc     OK" || { echo "ocamlc     FAILED"; sed -n '1,20p' "$adir/byte.build"; }
    ( cd "$adir" && "$OCAMLOPT" -w -a -c avatar_check.ml ) >"$adir/native.build" 2>&1 \
      && echo "ocamlopt   OK" || { echo "ocamlopt   FAILED"; sed -n '1,20p' "$adir/native.build"; }
    ( cd "$adir" && "$OCAMLC" -w -a -o chk.byte avatar_check.ml ) >>"$adir/byte.build" 2>&1 \
      && "$JSOO" compile --enable effects --target-env=nodejs "$adir/chk.byte" \
           -o "$adir/chk.js" >"$adir/jsoo.build" 2>&1 \
      && echo "js_of_ocaml OK" || { echo "js_of_ocaml FAILED"; sed -n '1,20p' "$adir/jsoo.build"; }
    # 2. each generated carrier, diffed against the hand-written avatar
    A="$REPO/workshop/OCaml5/avatar/deep_fibers.ml"
    G="$adir/generated.ml"
    check_block() {
      name=$1; first=$2; last=$3
      awk "/$first/,/$last/" "$A" > "$adir/a0.$name"
      awk "/$first/,/$last/" "$G" > "$adir/gen.$name"
      if [ ! -s "$adir/a0.$name" ]; then echo "$name: ABSENT from deep_fibers.ml"; return; fi
      if diff -q "$adir/a0.$name" "$adir/gen.$name" >/dev/null; then
        echo "$name: IDENTICAL to deep_fibers.ml"
      else
        echo "$name: DIFF"; diff "$adir/a0.$name" "$adir/gen.$name" | sed 's/^/    /'
      fi
    }
    check_block run_fiber     '^type run_fiber = \{'   '^\}'
    check_block frame_fiber   '^type frame_fiber = \{' '^\}'
    check_block observer      '^type observer ='        '^  \| Callback of int$'
    check_block run_event     '^type run_event ='       '^  \| Exited of int \* exitv$'
    check_block run_decision  '^type run_decision ='    '^  \| DinstallMiddleware$'
    ;;

  corpus)
    first=${2:-400000}; count=${3:-220}
    cdir="$REPO/workshop/OCaml5/fuzz/corpus"
    rm -rf "$cdir"; mkdir -p "$cdir"
    ( cd "$REPO" && $LEANRUN corpus "$cdir" "$first" "$count" ) || exit 1
    echo "corpus at $cdir"
    ;;

  corpus-smoke)
    sample=${2:-20}
    cdir="$REPO/workshop/OCaml5/fuzz/corpus"
    sdir="$P5_BUILD/corpus"
    rm -rf "$sdir"; mkdir -p "$sdir/ml" "$sdir/ts"
    total=$(ls -d "$cdir"/p* 2>/dev/null | wc -l | tr -d ' ')
    echo "corpus: $total programs"

    # (a) OCaml. The aggregate module holds every generated program, so one `ocamlc -c` of it
    #     typechecks the whole corpus against the avatar; the sample then checks that each
    #     per-program `fixture.ml` compiles on its own.
    cp "$REPO"/workshop/OCaml5/avatar/*.ml "$sdir/ml/" 2>/dev/null
    rm -f "$sdir/ml/jsprobe.ml"
    cp "$cdir/corpus_fixture.ml" "$sdir/ml/"
    # Seat W1: `deep_stores.ml` and `deep_layer.ml` are the ports of `Effect4/Deep/Stores.lean`
    # and `Layer.lean`, and the fixtures link against them.
    if ( cd "$sdir/ml" && "$OCAMLC" -c deep_fibers.ml deep_stores.ml deep_layer.ml \
           avatar_trace.ml fibers_fixture.ml store_fixtures.ml extra_fixture.ml ) \
         >"$sdir/avatar.build" 2>&1; then
      echo "ocamlc avatar modules   OK"
    else
      echo "ocamlc avatar modules   FAILED"; sed -n '1,20p' "$sdir/avatar.build"
    fi
    if ( cd "$sdir/ml" && "$OCAMLC" -c corpus_fixture.ml ) >"$sdir/agg.build" 2>&1; then
      echo "ocamlc corpus_fixture   OK ($total programs in one module)"
    else
      echo "ocamlc corpus_fixture   FAILED"; sed -n '1,20p' "$sdir/agg.build"
    fi
    ok=0; bad=0
    for d in $(ls -d "$cdir"/p* | head -"$sample"); do
      cp "$d/fixture.ml" "$sdir/ml/fixture.ml"
      if ( cd "$sdir/ml" && "$OCAMLC" -c fixture.ml ) >"$sdir/one.build" 2>&1; then
        ok=$((ok+1))
      else
        bad=$((bad+1)); echo "  ocamlc $(basename "$d") FAILED"; sed -n '1,8p' "$sdir/one.build"
      fi
    done
    echo "ocamlc per-program      $ok of $((ok+bad)) sampled"

    # (b) TypeScript, against the harness's compiler options.
    if [ ! -x "$TSC" ]; then
      echo "tsc                     SKIP (no $TSC)"
    else
      ln -s "$NODE_MODULES" "$sdir/ts/node_modules"
      cp "$cdir/corpus-fixture.ts" "$sdir/ts/"
      files='"corpus-fixture.ts"'
      for d in $(ls -d "$cdir"/p* | head -"$sample"); do
        n=$(basename "$d")
        cp "$d/fixture.ts" "$sdir/ts/$n.ts"
        files="$files, \"$n.ts\""
      done
      cat > "$sdir/ts/tsconfig.json" <<TSEOF
{
  "compilerOptions": {
    "strict": true,
    "target": "ES2022",
    "module": "ESNext",
    "moduleResolution": "bundler",
    "lib": ["ESNext", "DOM"],
    "types": [],
    "noEmit": true,
    "allowImportingTsExtensions": true,
    "exactOptionalPropertyTypes": true,
    "noUncheckedIndexedAccess": true,
    "verbatimModuleSyntax": true,
    "skipLibCheck": true
  },
  "files": [$files]
}
TSEOF
      if ( cd "$sdir/ts" && "$TSC" -p tsconfig.json ) >"$sdir/ts.build" 2>&1; then
        echo "tsc corpus-fixture      OK ($total programs) + $sample sampled fixtures"
      else
        echo "tsc                     FAILED"; sed -n '1,20p' "$sdir/ts.build"
      fi
    fi
    ;;

  tapes)
    seed=${2:-1}; count=${3:-50}; len=${4:-8}
    tdir="$P5_BUILD/tapes"
    rm -rf "$tdir"; mkdir -p "$tdir"
    ( cd "$REPO" && $LEANRUN tapes "$tdir" "$seed" "$count" "$len" ) || exit 1
    ( cd "$tdir" && "$OCAMLC" -w -a -c tapes.ml ) >"$tdir/byte.build" 2>&1 \
      && echo "ocamlc     OK" || { echo "ocamlc     FAILED"; sed -n '1,20p' "$tdir/byte.build"; }
    ( cd "$tdir" && "$OCAMLOPT" -w -a -c tapes.ml ) >"$tdir/native.build" 2>&1 \
      && echo "ocamlopt   OK" || { echo "ocamlopt   FAILED"; sed -n '1,20p' "$tdir/native.build"; }
    ( cd "$tdir" && "$OCAMLC" -w -a -o tapes.byte tapes.ml ) >>"$tdir/byte.build" 2>&1 \
      && "$JSOO" compile --enable effects --target-env=nodejs "$tdir/tapes.byte" \
           -o "$tdir/tapes.js" >"$tdir/jsoo.build" 2>&1 \
      && echo "js_of_ocaml OK" || { echo "js_of_ocaml FAILED"; sed -n '1,20p' "$tdir/jsoo.build"; }
    echo "wire: $tdir/tapes.wire"
    head -3 "$tdir/tapes.wire" | sed 's/^/    /'
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
