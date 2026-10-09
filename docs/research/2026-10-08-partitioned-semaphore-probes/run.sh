#!/bin/sh
# Run from the checkout root. No package installation or Lean build occurs.
set -eu
packet=docs/research/2026-10-08-partitioned-semaphore-probes
probe_tmp=$(mktemp -d)
trap 'rm -rf "$probe_tmp"' EXIT HUP INT TERM
python3 "$packet/input-fingerprints.py" > "$probe_tmp/inputs.json"
diff -u "$packet/inputs.json" "$probe_tmp/inputs.json"
/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/.bin/tsgo --project "$packet/tsconfig.json"
bun "$packet/host-controls.ts" > "$probe_tmp/observations.json"
diff -u "$packet/observations.json" "$probe_tmp/observations.json"
python3 - "$probe_tmp/observations.json" <<'PY'
import json
import sys
with open(sys.argv[1]) as f:
    d = json.load(f)
print(json.dumps({'positive': d['positive'], 'negative': d['negative'], 'retained_output_matches': True}))
PY
