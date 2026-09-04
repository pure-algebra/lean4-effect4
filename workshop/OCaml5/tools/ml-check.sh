#!/bin/sh
# Compile and run the `OCaml5.Ml` syntax fixture.
#
# Seat W3 of docs/research/2026-09-04-seat-w3-ml-api.md, check (a): every constructor of
# `OCaml5.Ml.Syntax` renders text OCaml accepts. `OCaml5.MlTest.main` writes the fixture and the
# rows it is expected to print; this script compiles the fixture on the three hosts of ruling 7
# and diffs what it prints against those rows.
#
#   tools/ml-check.sh           render, compile and run the fixture
#   tools/ml-check.sh --keep    …and say where the generated source is
#
# Verdicts:
#   ocamlc / ocamlopt / js_of_ocaml   OK or FAILED, with the first lines of the compiler's output
#   rows                              MATCH or DIFF against the pinned rows
#   ppxlib parse                      the rendered text parses as an OCaml implementation
#   ppx_jane                          the deriving fixture typechecks with the derivers applied
#   ocamlformat                       informational: how far the renderer is from the canonical
#                                     printer (see the note below)
#
# The last three need the `effect4` opam switch of
# docs/research/2026-09-04-ocaml-packages-plan.md and SKIP until it exists. Nothing here
# installs anything.
#
# ON OCAMLFORMAT, A CHOICE AND NOT A SILENCE. The canonical printer for the estate's generated
# OCaml is `OCaml5.Ml.Render`, not `ocamlformat`, and the reason is the check that matters most:
# `tools/fuzz.sh avatar` diffs the generated carriers byte for byte against
# `workshop/OCaml5/avatar/deep_fibers.ml`, which is hand-written in its own layout. Adopting
# ocamlformat as canonical would mean reformatting that file first, and the diff would then be
# testing ocamlformat rather than the generator. So the lane below is INFORMATIONAL: it reports
# how many lines the two printers disagree on and never fails the run. If the avatar is ever
# reformatted, flip it to a gate and delete this paragraph.
#
# `ocamlc` runs with **default warnings**, not `-w -a`: a generated module that warns is a
# generated module a consumer has to silence, so the fixture carries its own
# `[@@@warning "-a"]` and nothing here hides one.
#
# Build products go under $P5_BUILD (default: the session scratchpad), never into the
# repository. Environment: OCAMLC, OCAMLOPT, OCAMLRUN, JSOO, NODE, P5_BUILD.

set -u

REPO=$(cd "$(dirname "$0")/../../.." && pwd)
OCAMLC=${OCAMLC:-/Users/pooks/.opam/default/bin/ocamlc}
OCAMLOPT=${OCAMLOPT:-/Users/pooks/.opam/default/bin/ocamlopt}
OCAMLRUN=${OCAMLRUN:-/Users/pooks/.opam/default/bin/ocamlrun}
JSOO=${JSOO:-/Users/pooks/Dev/effect4_of_ocaml/_build/toolchains/ocaml5-jsoo-5.7.1/_build/default/vendor/js_of_ocaml-compiler.5.7.1/compiler/bin-js_of_ocaml/js_of_ocaml.exe}
NODE=${NODE:-node}
P5_BUILD=${P5_BUILD:-/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/d87ba830-2e63-4750-815f-2679b36f870a/scratchpad/p5}

dir="$P5_BUILD/ml"
rm -rf "$dir"; mkdir -p "$dir" || exit 1

( cd "$REPO" && lake env lean --run workshop/OCaml5/MlTest.lean "$dir" ) || exit 1

status=0

# 1. bytecode, and the rows
if ( cd "$dir" && "$OCAMLC" -o fixture.byte ml_fixture.ml ) >"$dir/byte.build" 2>&1; then
  echo "ocamlc      OK"
else
  echo "ocamlc      FAILED"; sed -n '1,25p' "$dir/byte.build"; status=1
fi

if [ -f "$dir/fixture.byte" ]; then
  ( cd "$dir" && "$OCAMLRUN" fixture.byte ) >"$dir/byte.rows" 2>"$dir/byte.err"
  if diff -q "$dir/ml_fixture.rows" "$dir/byte.rows" >/dev/null; then
    echo "rows        MATCH ($(wc -l < "$dir/ml_fixture.rows" | tr -d ' ') rows)"
  else
    echo "rows        DIFF"; diff "$dir/ml_fixture.rows" "$dir/byte.rows" | sed 's/^/    /'
    status=1
  fi
fi

# 2. native
if ( cd "$dir" && "$OCAMLOPT" -o fixture.native ml_fixture.ml ) >"$dir/native.build" 2>&1; then
  echo "ocamlopt    OK"
else
  echo "ocamlopt    FAILED"; sed -n '1,25p' "$dir/native.build"; status=1
fi

# 3. js_of_ocaml, with the effects backend of ruling 7
if [ -f "$dir/fixture.byte" ] && [ -x "$JSOO" ]; then
  if "$JSOO" compile --enable effects --target-env=nodejs "$dir/fixture.byte" \
       -o "$dir/fixture.js" >"$dir/jsoo.build" 2>&1; then
    ( cd "$dir" && "$NODE" fixture.js ) >"$dir/jsoo.rows" 2>"$dir/jsoo.err"
    if diff -q "$dir/ml_fixture.rows" "$dir/jsoo.rows" >/dev/null; then
      echo "js_of_ocaml OK"
    else
      echo "js_of_ocaml ROWS DIFF"; diff "$dir/ml_fixture.rows" "$dir/jsoo.rows" | sed 's/^/    /'
      status=1
    fi
  else
    echo "js_of_ocaml FAILED"; sed -n '1,25p' "$dir/jsoo.build"; status=1
  fi
else
  echo "js_of_ocaml SKIP"
fi

# 4. ppxlib: the rendered text parses as an OCaml implementation. A stronger statement than
#    "ocamlc accepted it", because it is the AST the estate's own tooling would consume.
OCAMLFIND=${OCAMLFIND:-ocamlfind}
if command -v "$OCAMLFIND" >/dev/null 2>&1 \
   && "$OCAMLFIND" query ppxlib >/dev/null 2>&1; then
  cat > "$dir/ml_parse.ml" <<'PARSEEOF'
let parse file =
  let ic = open_in file in
  let lb = Lexing.from_channel ic in
  Lexing.set_filename lb file;
  let (_ : Ppxlib.Parsetree.structure) = Ppxlib.Parse.implementation lb in
  close_in ic;
  print_endline ("parsed " ^ file)

let () = Array.iteri (fun i f -> if i > 0 then parse f) Sys.argv
PARSEEOF
  if ( cd "$dir" && "$OCAMLFIND" ocamlc -package ppxlib -linkpkg -o ml_parse ml_parse.ml ) \
       >"$dir/parse.build" 2>&1 \
     && ( cd "$dir" && ./ml_parse ml_fixture.ml ml_deriving.ml ) >"$dir/parse.out" 2>&1; then
    echo "ppxlib      OK ($(wc -l < "$dir/parse.out" | tr -d ' ') files parsed)"
  else
    echo "ppxlib      FAILED"; sed -n '1,25p' "$dir/parse.build" "$dir/parse.out" 2>/dev/null
    status=1
  fi
else
  echo "ppxlib      SKIP (no ocamlfind/ppxlib: the effect4 switch is not built yet)"
fi

# 5. ppx_jane: the deriving fixture, which plain ocamlc cannot compile.
if command -v "$OCAMLFIND" >/dev/null 2>&1 \
   && "$OCAMLFIND" query ppx_jane >/dev/null 2>&1; then
  if ( cd "$dir" && "$OCAMLFIND" ocamlc -package core,ppx_jane -c ml_deriving.ml ) \
       >"$dir/ppx.build" 2>&1; then
    echo "ppx_jane    OK"
  else
    echo "ppx_jane    FAILED"; sed -n '1,25p' "$dir/ppx.build"; status=1
  fi
else
  echo "ppx_jane    SKIP (no ocamlfind/ppx_jane: the effect4 switch is not built yet)"
fi

# 6. ocamlformat, informational only. See the note at the top of this file.
OCAMLFORMAT=${OCAMLFORMAT:-ocamlformat}
if command -v "$OCAMLFORMAT" >/dev/null 2>&1; then
  if "$OCAMLFORMAT" --enable-outside-detected-project --profile=janestreet \
       --name ml_fixture.ml "$dir/ml_fixture.ml" >"$dir/ml_fixture.fmt" 2>"$dir/fmt.err"; then
    n=$(diff "$dir/ml_fixture.ml" "$dir/ml_fixture.fmt" | grep -c '^[<>]')
    if [ "$n" = "0" ]; then
      echo "ocamlformat IDENTICAL (informational)"
    else
      echo "ocamlformat $n lines differ (informational; the renderer is canonical, not this)"
    fi
  else
    echo "ocamlformat FAILED to format (informational)"; sed -n '1,10p' "$dir/fmt.err"
  fi
else
  echo "ocamlformat SKIP (not installed: the effect4 switch is not built yet)"
fi

if [ "${1:-}" = "--keep" ]; then echo "source      $dir/ml_fixture.ml"; fi
exit "$status"
