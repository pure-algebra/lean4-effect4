#!/usr/bin/env bash
# Seat S, question 5: split the dedupe probe's output into files, compare the three harness
# fixtures with the committed generated files, and check the meta-schema module with and without
# (C) under tsgo 7 and bun.
set -u
cd "$(dirname "$0")"
root=/Users/pooks/Dev/lean4-effect4-probe-S
python3 - <<'PY'
import re
log = open('../logs/refdedupe.log').read()
for m in re.finditer(r'=====BEGIN (\S+)\n(.*?)=====END\n', log, re.S):
    open('q5/' + m.group(1), 'w').write(m.group(2))
    print('wrote q5/' + m.group(1), len(m.group(2).encode()), 'bytes')
PY
for f in Person.generated.ts AllRepresentations.generated.ts TwoRoots.generated.ts; do
  if cmp -s "q5/$f" "$root/harness/schema-generation/$f"; then echo "identical: $f (committed $(wc -c < "$root/harness/schema-generation/$f") bytes)"; else echo "DIFFERS: $f"; fi
done
