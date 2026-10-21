#!/bin/sh
# Measure the native lowering two ways, with the tree's own producers, and count the closures.
#
#   docs/research/2026-10-21-host-runtime-design/closure.sh > docs/research/2026-10-21-host-runtime-design/closure.out
#
# 1. Today: `lake exe effect4 emit --group todo --target ocaml`, which lowers the five roots that
#    `Compiler.Groups.todoLowered` names (`tools/Compiler/Groups.lean`).
# 2. Proposed: `lake exe lcnfgen --project-recipe recipe-engine.json`: an engine of seven library
#    roots, then the to-do's typed host adapter and its Lean model, each using the engine.
# 3. The object's node bytes: `recipe-load.json` lowers `Object.load` and `Object.bytes` alone. The
#    producer refuses it, and the script reports the declarations it has no translation for.
# 4. Today's Lean run of the to-do script (`lake exe effect4 run --group todo --typed`), the
#    baseline that the landing's acceptance compares with.
# Every output goes to a scratch directory; nothing in the tree is written. A closure manifest's
# first two lines are its header, so its declarations are its other lines.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
WORK=${TMPDIR:-/tmp}/effect4-host-runtime-closure
rm -rf "$WORK"
mkdir -p "$WORK/today" "$WORK/engine" "$WORK/load"
cd "$ROOT"
export LEAN_NUM_THREADS=3
lake exe effect4 emit --group todo --target ocaml --out "$WORK/today" > "$WORK/today.log" 2>&1
lake exe lcnfgen --stage "$WORK/engine" --project-recipe "$HERE/recipe-engine.json" > "$WORK/engine.log" 2>&1
if lake exe lcnfgen --stage "$WORK/load" --project-recipe "$HERE/recipe-load.json" > "$WORK/load.log" 2>&1; then
  LOAD=lowered
else
  LOAD=refused
fi
decls() { awk 'NR>2' "$1" | wc -l | tr -d ' '; }
tests() { awk -F'\t' 'NR>2 && $1 ~ /^Test\./' "$1" | wc -l | tr -d ' '; }
lines() { wc -l < "$1" | tr -d ' '; }
names() { awk -F'\t' 'NR>2{print $1}' "$1" | LC_ALL=C sort -u; }
echo "today: lowering.json roots:"
sed 's/.*"linkage":\[//; s/\].*//' "$WORK/today/lowering.json" | tr ',' '\n' | sed 's/^/  /'
echo "today: todo_gen.ml $(lines "$WORK/today/todo_gen.ml") lines, $(decls "$WORK/today/closure-todo_gen.tsv") declarations, $(tests "$WORK/today/closure-todo_gen.tsv") under Test"
for unit in engine_gen todo_host_gen todo_model_gen; do
  echo "proposed: $unit.ml $(lines "$WORK/engine/$unit.ml") lines, $(decls "$WORK/engine/closure-$unit.tsv") declarations, $(tests "$WORK/engine/closure-$unit.tsv") under Test"
done
names "$WORK/today/closure-todo_gen.tsv" > "$WORK/today.names"
names "$WORK/engine/closure-engine_gen.tsv" > "$WORK/engine.names"
awk -F'\t' 'NR>2{print $1 "\t" $NF}' ocaml/gen/closure-api_gen.tsv | LC_ALL=C sort -u > "$WORK/api.units"
echo "today's declarations the engine lowers too: $(LC_ALL=C comm -12 "$WORK/today.names" "$WORK/engine.names" | wc -l | tr -d ' ')"
echo "today's declarations outside the engine, by namespace:"
LC_ALL=C comm -23 "$WORK/today.names" "$WORK/engine.names" | awk -F. '{print $1"."$2"."$3}' | sort | uniq -c | sort -rn | sed 's/^/  /'
echo "the engine's declarations in ocaml/gen/closure-api_gen.tsv, by compilation unit:"
LC_ALL=C join -t "$(printf '\t')" "$WORK/engine.names" "$WORK/api.units" | awk -F'\t' '{print $2}' | sort | uniq -c | sed 's/^/  /'
echo "the engine's declarations that only the test lanes' unit lowers today:"
LC_ALL=C join -t "$(printf '\t')" "$WORK/engine.names" "$WORK/api.units" | awk -F'\t' '$2 == "Lanes_gen" {print "  " $1}'
echo "the engine's declarations not in ocaml/gen/closure-api_gen.tsv:"
LC_ALL=C join -t "$(printf '\t')" -v 1 "$WORK/engine.names" "$WORK/api.units" | sed 's/^/  /'
echo "the object's node reader and writer alone: $LOAD; $(grep '^closure:' "$WORK/load.log")"
grep -A 20 '^todos' "$WORK/load.log" | grep ': extern' | sed 's/^ */  no translation: /'
echo "today's run of the to-do script (lake exe effect4 run --group todo --typed):"
lake exe effect4 run --group todo --typed 2>&1 | sed 's/^/  /'
