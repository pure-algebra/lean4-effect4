#!/usr/bin/env bash
# A0: build the avatar (native, bytecode and js_of_ocaml effects mode), run every fiber
# golden's program on every host, and compare all three faces with the Lean golden under
# every mask in `generated/traces/masks.tsv`.
#
# Nothing under `harness/trace/` or `scripts/` is touched: the rc.112 face is produced by
# invoking the estate's own runner (`effect4-tools/packages/harness/trace.mjs` with
# `--tail fiber-tail.ts`), exactly as `scripts/check-trace-host.sh` does, and the avatar's
# face is compared by `compare.py` here, which reimplements `trace.mjs`'s `project`/compare.
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(CDPATH= cd -- "$here/../../.." && pwd)
out=${A0_BUILD:-/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/d87ba830-2e63-4750-815f-2679b36f870a/scratchpad/a0}
oc=${OCAML5_BIN:-/Users/pooks/.opam/default/bin}
jsoo=${JSOO5_BIN:-/Users/pooks/Dev/effect4_of_ocaml/_build/toolchains/ocaml5-jsoo-5.7.1/_build/default/vendor/js_of_ocaml-compiler.5.7.1/compiler/bin-js_of_ocaml/js_of_ocaml.exe}
tools=${EFFECT4_TOOLS:-$repo/../effect4-tools}
traces="$repo/generated/traces/fiber"
masks="$repo/generated/traces/masks.tsv"

mkdir -p "$out/build" "$here/out"
cp "$here"/*.ml "$out/build/"
cd "$out/build"

modules="deep_fibers.ml avatar_trace.ml fibers_fixture.ml avatar_main.ml"
"$oc/ocamlc"   -o avatar.byte   $modules
"$oc/ocamlopt" -o avatar.native $modules
"$jsoo" compile --enable effects --target-env=nodejs avatar.byte -o avatar.js 2>/dev/null

sha=$(cat "$here"/*.ml "$here/build-avatar.sh" | shasum -a 256 | cut -d' ' -f1)
pin=$(awk -F'\t' '$1=="pin"{print $3}' "$traces/awaitValueDistinctFromJoinEffect.tsv" | head -1)

for golden in "$traces"/*.tsv; do
  program=$(basename "$golden" .tsv)
  tape=$(awk -F'\t' '$1=="tape"{print $2}' "$golden")
  rules=$(awk -F'\t' '$1=="rules"{print $2}' "$golden")
  env EFFECT4_PROGRAM="$program" EFFECT4_TAPE="$tape" EFFECT4_RULES="$rules" \
      EFFECT4_PIN="$pin" EFFECT4_SHA="$sha" \
      "$oc/ocamlrun" ./avatar.byte > "$here/out/$program.ocaml.tsv"
  env EFFECT4_PROGRAM="$program" EFFECT4_TAPE="$tape" EFFECT4_RULES="$rules" \
      EFFECT4_PIN="$pin" EFFECT4_SHA="$sha" \
      ./avatar.native > "$out/build/$program.native.tsv"
  env EFFECT4_PROGRAM="$program" EFFECT4_TAPE="$tape" EFFECT4_RULES="$rules" \
      EFFECT4_PIN="$pin" EFFECT4_SHA="$sha" \
      node avatar.js > "$out/build/$program.jsoo.tsv"
  env EFFECT4_PROGRAM="$program" EFFECT4_TAPE="$tape" EFFECT4_EVENTS=1 EFFECT4_STATUS=1 \
      EFFECT4_RULES="$rules" EFFECT4_PIN="$pin" EFFECT4_SHA="$sha" \
      "$oc/ocamlrun" ./avatar.byte > "$here/out/$program.events.tsv"
done

# --- deliverable 2: the JS closure boundary -----------------------------------
mkdir -p "$out/js"
cp "$here/jsprobe.ml" "$here/jsprobe_runtime.js" "$out/js/"
( cd "$out/js"
  "$oc/ocamlc" -no-check-prims -o jsprobe.byte jsprobe.ml
  "$jsoo" compile --enable effects --target-env=nodejs jsprobe_runtime.js jsprobe.byte \
    -o jsprobe.js 2>/dev/null
  node jsprobe.js ) > "$here/out/jsprobe.out" 2>&1 || true
# Negative control: the same bytecode with the effects transform off.
( cd "$out/js"
  "$jsoo" compile --target-env=nodejs jsprobe_runtime.js jsprobe.byte \
    -o jsprobe-noeffects.js 2>/dev/null
  node jsprobe-noeffects.js ) > "$here/out/jsprobe-noeffects.out" 2>&1 || true

echo "=== three OCaml hosts agree (bytecode / native / js_of_ocaml --enable effects)"
status=0
for golden in "$traces"/*.tsv; do
  program=$(basename "$golden" .tsv)
  if cmp -s "$here/out/$program.ocaml.tsv" "$out/build/$program.native.tsv" &&
     cmp -s "$here/out/$program.ocaml.tsv" "$out/build/$program.jsoo.tsv"; then
    echo "hosts $program AGREE"
  else
    echo "hosts $program DISAGREE"; status=1
  fi
done

echo "=== ocaml face vs lean golden, under every mask"
python3 "$here/compare.py" --masks "$masks" --goldens "$traces" --face "$here/out" --suffix .ocaml.tsv || status=1

echo "=== rc.112 host face vs lean golden, through the estate's own runner"
if [ -d "$tools" ]; then
  for golden in "$traces"/*.tsv; do
    program=$(basename "$golden" .tsv)
    env EFFECT4_PROGRAM="$program" node "$tools/packages/harness/trace.mjs" "$repo/harness/trace" \
      --golden "$golden" --masks "$masks" --tail fiber-tail.ts || status=1
  done
else
  echo "SKIP effect4-tools not present at $tools"
fi
exit $status
