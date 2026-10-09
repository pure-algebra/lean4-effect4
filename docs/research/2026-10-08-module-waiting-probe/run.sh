#!/bin/sh
set -eu
packet=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
probe_tmp=$(mktemp -d)
trap 'rm -rf "$probe_tmp"' EXIT HUP INT TERM
python3 "$packet/input-fingerprints.py" > "$probe_tmp/inputs.json"
cmp "$packet/inputs.json" "$probe_tmp/inputs.json"
/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/.bin/tsgo --project "$packet/tsconfig.json"
bun "$packet/host-controls.ts" > "$probe_tmp/observations.json"
cmp "$packet/observations.json" "$probe_tmp/observations.json"
python3 - "$probe_tmp/observations.json" <<'PY'
import json
from pathlib import Path
import sys
p = json.loads(Path(sys.argv[1]).read_text())
assert p['positive'] > 0 and p['negative'] > 0
print(json.dumps({'positive': p['positive'], 'negative': p['negative'], 'retained_output_matches': True}))
PY
