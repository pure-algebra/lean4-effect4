#!/usr/bin/env python3
"""Read-only source checks and isolated model reruns for the follow-up packet."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPO = Path('/Users/pooks/Dev/lean4-effect4')
checks = []

def sha(data):
    return hashlib.sha256(data).hexdigest()

def record(label, ok, **detail):
    checks.append({'name': label, 'pass': bool(ok), **detail})
    if not ok:
        raise AssertionError(label)

def git_bytes(repo, commit, path):
    return subprocess.check_output(['git', '-C', str(repo), 'show', f'{commit}:{path}'])

def verify_source(entry, base, revision_key, snapshot_key, repo=REPO):
    snap = Path(entry[snapshot_key])
    if not snap.is_absolute():
        snap = base / snap
    copied = snap.read_bytes()
    original = git_bytes(repo, entry[revision_key], entry['path'])
    record(f"source:{entry[revision_key]}:{entry['path']}",
           original == copied and sha(copied) == entry['sha256'], kind='committed-source')

focus = ROOT / 'next-slices/focus'
for entry in json.loads((focus / 'manifest.json').read_text())['sources']:
    verify_source(entry, focus, 'revision', 'snapshot')

rewrite = ROOT / 'next-slices/loop-rewrite'
for entry in json.loads((rewrite / 'source-manifest.json').read_text())['files']:
    verify_source(entry, rewrite, 'commit', 'snapshot')

for entry in json.loads((ROOT / 'transition/source-evidence-manifest.json').read_text()):
    if entry['kind'] == 'committed-source':
        verify_source(entry, ROOT / 'transition', 'commit', 'copy', Path(entry['repository']))
    else:
        copied = Path(entry['copy']).read_bytes()
        record(f"snapshot:{entry['copy']}", sha(copied) == entry['sha256'], kind=entry['kind'],
               note='Historical snapshot identity; not acceptance of later live source or a monitor rerun')

review = json.loads((ROOT / 'interop/final-route-review-receipt.json').read_text())
for entry in review['sources']:
    original = git_bytes(REPO, entry['commit'], entry['path'])
    record(f"final-route:{entry['path']}", sha(original) == entry['sha256'], kind='route-source')
for entry in review['reviewed_artifacts']:
    record(f"review-artifact:{entry['path']}", sha(Path(entry['path']).read_bytes()) == entry['sha256'], kind='review-artifact')

models = [
    (focus / 'probe.py', focus / 'probe-results.json', 24, 'passed'),
    (rewrite / 'model-controls.py', rewrite / 'model-controls-output.json', 142, 'checks'),
]
for script, output, expected, field in models:
    prior = json.loads(output.read_text())
    proc = subprocess.run([sys.executable, str(script)], check=True, capture_output=True, text=True)
    actual = json.loads(output.read_text())
    count = len(actual[field]) if isinstance(actual[field], list) else actual[field]
    record(f'model:{script.name}', actual == prior and count == expected,
           count=count, stdout=proc.stdout.strip(), kind='isolated-finite-model')

clock_path = ROOT / 'transition/clock-results.json'
prior = json.loads(clock_path.read_text())
clock_proc = subprocess.run([sys.executable, str(ROOT / 'transition/clock_controls.py')],
                            check=True, capture_output=True, text=True)
actual = json.loads(clock_proc.stdout)
record('model:clock_controls.py', actual == prior and actual['count'] == 8,
       count=actual['count'], kind='isolated-finite-model')

head = subprocess.check_output(['git', '-C', str(REPO), 'rev-parse', 'HEAD'], text=True).strip()
registry = git_bytes(REPO, head, 'tools/Tools/SemanticsRegistry.lean').decode()
start = registry.index('    { id := "R1", title :=')
end = registry.index('\n  ]\n  planScope', start)
block = registry[start:end] + '\n'
record('closing-full-requirements', block == (ROOT / 'requirements-source.txt').read_text(), kind='requirements', commit=head)
for n in range(1, 14):
    marker = f'{{ id := "R{n}", title :='
    part = block.split(marker, 1)[1]
    if n < 13:
        part = part.split(f'{{ id := "R{n+1}", title :=', 1)[0]
    record(f'closing-requirement:R{n}', block.count(marker) == 1 and 'openParts := [' in part, kind='requirements')
closing = ROOT / 'transition/closing-source'
closing.mkdir(exist_ok=True)
for path in ['docs/core/decisions.md', 'docs/STATE.md',
             'docs/research/2026-10-05-claude-lead/2026-10-06-transition-account.md']:
    original = git_bytes(REPO, head, path)
    dest = closing / Path(path).name
    dest.write_bytes(original)
    record(f'closing:{path}', original == dest.read_bytes(), kind='closing-source',
           commit=head, sha256=sha(original), snapshot=str(dest))

summary = {
    'all_pass': all(c['pass'] for c in checks),
    'checks': len(checks),
    'committed_source_comparisons': sum(c['kind'] == 'committed-source' for c in checks),
    'historical_snapshot_comparisons': sum(c['kind'] in ['retained-seat-output','active-source'] for c in checks),
    'additional_route_source_comparisons': sum(c['kind'] == 'route-source' for c in checks),
    'closing_source_comparisons': sum(c['kind'] == 'closing-source' for c in checks),
    'finite_model_controls': 24 + 142 + 8,
    'closing_commit': head,
    'not_performed': ['Lean', 'project build', 'compiler', 'Effect or target runtime',
                      'generator', 'installation', 'implementation repository edits'],
    'results': checks,
}
(ROOT / 'next-verification.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k:v for k,v in summary.items() if k != 'results'}, indent=2))
