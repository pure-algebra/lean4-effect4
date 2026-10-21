"""Read closure counts from the generated manifests; never infer native execution."""
import json
import os
from pathlib import Path

work = Path(os.environ.get('TMPDIR', '/tmp'))
def names(path):
    return {line.split('\t')[0] for line in path.read_text().splitlines()[2:]}

base = work / 'effect4-host-runtime-closure/engine/closure-engine_gen.tsv'
guarded = work / 'guarded-engine/closure-guarded_engine_gen.tsv'
a, b = names(base), names(guarded)
print(json.dumps({
    'engine_declarations': len(a),
    'guarded_engine_declarations': len(b),
    'guard_added': sorted(b - a),
    'guard_removed': sorted(a - b),
    'guarded_generated_lines': len(guarded.with_name('guarded_engine_gen.ml').read_text().splitlines()),
}, indent=2))
