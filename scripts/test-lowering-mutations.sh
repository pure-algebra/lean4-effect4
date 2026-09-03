#!/usr/bin/env bash
# Plants three lowering mutants in a temp copy of the property corpus and
# requires the batch to catch each: the arms of one choose site swapped, one
# site's decision ignored (the tape not consulted), and an off-by-one tape
# cursor. The committed sources are never edited.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
tools="${EFFECT4_TOOLS:-$repo_root/../effect4-tools}"
here="$repo_root/harness/trace"
seed="${EFFECT4_PROPERTY_SEED:-2026}"; count="${EFFECT4_MUTATION_COUNT:-40}"
cd "$repo_root"
lake build Effect4 >/dev/null
tmp="$(mktemp -d "${TMPDIR:-/tmp}/effect4-mutations.XXXXXX")"; trap 'rm -rf -- "$tmp"' EXIT
mkdir -p "$tmp/corpus"
cp "$here/tracer.ts" "$here/atoms.ts" "$here/property-tail.ts" "$here/property-structured-tail.ts" "$here/host-pin.json" "$tmp/corpus/"
# Discarding Lean's stdout discards Lean's errors with it -- they are printed
# there, not on stderr -- so this gate once exited 1 with an empty log while
# Property.lean had a missing-cases error. `lean_run` (scripts/lib/portable.sh)
# names the failure and reprints everything Lean wrote.
lean_run "$here/Property.lean" corpus "$seed" "$count" "$tmp/corpus" >/dev/null
batch() { node "$tools/packages/harness/batch.mjs" "$1" --goldens "$1/goldens" --masks "$repo_root/generated/traces/masks.tsv" --tail property-tail.ts; }
batch "$tmp/corpus" > "$tmp/clean.log" 2>&1 || { echo "FAIL the unmutated corpus does not pass" >&2; cat "$tmp/clean.log" >&2; exit 1; }
caught=0; total=3
mutate() { # file, pattern, replacement: replace the first match of the regex
  python3 - "$1" "$2" "$3" <<'PY'
import re, sys
path, pattern, replacement = sys.argv[1:4]
text = open(path).read()
new = re.sub(pattern, replacement, text, count=1)
if new == text: sys.exit(1)
open(path, "w").write(new)
PY
}
expect() { # name, file, pattern, replacement
  local name="$1" file="$2" pattern="$3" replacement="$4"
  rm -rf "$tmp/$name" && cp -R "$tmp/corpus" "$tmp/$name"
  mutate "$tmp/$name/$file" "$pattern" "$replacement" || { echo "FAIL mutant $name did not change the corpus" >&2; exit 1; }
  if batch "$tmp/$name" > "$tmp/$name.log" 2>&1; then echo "FAIL mutant $name survived the property batch" >&2; exit 1; fi
  grep -q "DIVERGES" "$tmp/$name.log" || { echo "FAIL mutant $name failed for an unrelated reason" >&2; cat "$tmp/$name.log" >&2; exit 1; }
  echo "PASS mutant $name caught: $(grep -c DIVERGES "$tmp/$name.log") diverging mask rows"; caught=$((caught + 1))
}
# 1. swap the arms of the first choose site: `if (c0)` becomes `if (!c0)`
expect swapped-arms property-fixture.ts 'if \((c[0-9]+)\) \{' 'if (!\1) {'
# 2. ignore the tape at the first site: the decision is always true
expect ignored-tape property-fixture.ts 'yield\* decisions\.choose\([0-9]+\)' 'true'
# 3. an off-by-one tape cursor in the host's Decisions service
expect off-by-one-cursor tracer.ts 'let cursor = 0' 'let cursor = 1'
# 4. the structured form: a `continue` to the wrong loop label becomes a `break`
batch_structured() { node "$tools/packages/harness/batch.mjs" "$1" --goldens "$1/goldens" --masks "$repo_root/generated/traces/masks.tsv" --tail property-structured-tail.ts; }
total=4
rm -rf "$tmp/swapped-continue" && cp -R "$tmp/corpus" "$tmp/swapped-continue"
mutate "$tmp/swapped-continue/property-structured-fixture.ts" 'continue (W[0-9]+)' 'break \1' || { echo "FAIL mutant swapped-continue did not change the corpus" >&2; exit 1; }
if batch_structured "$tmp/swapped-continue" > "$tmp/swapped-continue.log" 2>&1; then echo "FAIL mutant swapped-continue survived" >&2; exit 1; fi
grep -q "DIVERGES" "$tmp/swapped-continue.log" || { echo "FAIL mutant swapped-continue failed for an unrelated reason" >&2; cat "$tmp/swapped-continue.log" >&2; exit 1; }
echo "PASS mutant swapped-continue caught: $(grep -c DIVERGES "$tmp/swapped-continue.log") diverging mask rows"; caught=$((caught + 1))
echo "PASS lowering mutants caught $caught/$total"
