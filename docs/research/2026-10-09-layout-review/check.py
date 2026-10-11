"""Record the measured layout review evidence; refuse missing or changed observations."""
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import subprocess

folder = Path(__file__).resolve().parent
repo = folder.parents[2]
base = '28ed6727e1979b544a4d9c619cc837509511c0b6'
reviewed = 'bfe97080657ecb87d4551fc8a4511580369f698d'


def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)


expected_names = '''unique-keys-lookup
duplicate-keys-lookup
unique-keys-rendered-edges-descend
duplicate-keys-rendered-edges-descend
duplicate-keys-boxes-still-apart
zero-width-admitted-premise
negative-width-outside-premise
sample-cross-wait-present
sample-cross-wait-order-accepted
sample-cross-wait-height-met
cycle-wait-present
cycle-wait-retained-as-lane
cycle-wait-does-not-constrain-height
cycle-own-edges-descend
empty-layout-dimensions
parallel-edge-counts'''.splitlines()
rows = json.loads((folder / 'controls.json').read_text())
require([r['name'] for r in rows] == expected_names, 'control inventory changed')
require(all(r['pass'] is True and r['actual'] == r['expected'] for r in rows), 'a control disagrees')
axioms = (folder / 'axioms.txt').read_text().splitlines()
names = ['lay_good', 'assign_meets', 'place_descends', 'place_apart']
require(axioms == [f"'Tools.View.Flow.{n}' depends on axioms: [propext, Quot.sound]" for n in names],
        'landed theorem trust output differs')

before = folder / 'out-before'
after = folder / 'out-after'
files_a = {p.relative_to(before): p.read_bytes() for p in before.rglob('*') if p.is_file()}
files_b = {p.relative_to(after): p.read_bytes() for p in after.rglob('*') if p.is_file()}
require(files_a and files_a.keys() == files_b.keys(), 'drawing inventories differ or are empty')
require({p.parts[0] for p in files_a} ==
        {'p42', 'pBind', 'pFork', 'pAwait', 'pGen', 'pLoop', 'pCatch', 'pScope', 'flows', 'specimen'},
        'missing drawing families')
require(all(p.suffix in {'.svg', '.draw', '.txt'} for p in files_a), 'unexpected drawing format')
require(all(content == files_b[path] for path, content in files_a.items()), 'drawing bytes differ')
page_stems = {p.with_suffix('') for p in files_a}
require(all({str(p) + suffix for suffix in ('.svg', '.draw', '.txt')} <= {str(k) for k in files_a}
            for p in page_stems), 'a page lacks an output format')
require((folder / 'snapshot-before.txt').read_bytes() == (folder / 'snapshot-after.txt').read_bytes(),
        'snapshot page counts differ')
changed = subprocess.check_output(['git', 'diff', '--name-only', reviewed, '--', '.', ':!docs/research'], cwd=repo)
require(not changed.strip(), 'tracked production files changed in the review checkout')

manifest = {'baseCommit': base, 'reviewedCommit': reviewed,
            'checkedAtUtc': datetime.now(timezone.utc).isoformat(),
            'controlCount': len(rows), 'allExpectedObservationsMatched': True,
            'pageCount': len(page_stems), 'identicalFileCount': len(files_a),
            'formats': ['SVG', 'device calls', 'page text'],
            'axiomDependencies': {n: ['propext', 'Quot.sound'] for n in names},
            'openFindings': {
                'D3R-1': 'Correct accepted-wait coverage and theorem names/premises in the source comments and note.',
                'D3R-2': 'The linear-cost design claim predates this landing; alignment edges grow quadratically.'},
            'acknowledgedOpenConnection': 'Structural positions to key-resolved routes, under unique keys.',
            'priorCheckpoint': {'commit': '7e22063f', 'MCR-1-through-MCR-5': 'unchanged; no MCP implementation change in this landing'},
            'limits': ['No runtime-order or deadlock theorem is established.',
                       'No native window, animation, browser or whole-tree sweep is exercised.',
                       'Synthetic duplicate keys are outside the documented drawing connection premise.'],
            'drawingSha256': {str(p): sha256(files_a[p]).hexdigest() for p in sorted(files_a)},
            'sourceSha256': {name: sha256((folder / name).read_bytes()).hexdigest()
                             for name in ['Axioms.lean', 'Controls.lean', 'Snapshot.lean', 'check.py']}}
(folder / 'checkpoint.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(f'PASS: {len(rows)} controls, {len(page_stems)} pages, {len(files_a)} identical files, '
      f'{len(names)} theorem trust results; production source unchanged.')
