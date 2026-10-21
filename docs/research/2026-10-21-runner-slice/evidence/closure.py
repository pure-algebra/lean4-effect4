"""Read-only reach check for the runner slice's existing native artifacts."""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'scripts'))
from lib.lean_imports import source_closure

recipe = json.loads((ROOT / 'ocaml/gen/roots.json').read_text())
roots = [name for artifact in recipe['artifacts'] for name in artifact.get('import', [])]
closure = set(source_closure(ROOT, roots, None))
new = {'src/Effect4/Run/Runner.lean', 'src/Effect4/Laws/Run/Runner.lean'}
reached = sorted(closure & new)
print('New runner modules in lowering import closure:', reached)
assert not reached
prefixes = ('Effect4.Api.ServiceSession.', 'Effect4.Run.Reactor.tensor', 'Effect4.Run.Reactor.queue')
for path in sorted((ROOT / 'ocaml/gen').glob('closure-*.tsv')):
    lines = [line for line in path.read_text().splitlines()
             if line and not line.startswith(('#', 'lean\t'))]
    hits = [line.split('\t', 1)[0] for line in lines if line.startswith(prefixes)]
    print(f'{path.relative_to(ROOT)}: {len(lines)} declarations; changed-family hits: {hits}')
    assert not hits
print('PASS: no changed executable declaration reaches an existing native artifact.')
