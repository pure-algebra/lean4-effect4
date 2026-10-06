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

def record(name, ok, **fields):
    assert ok, (name, fields)
    checks.append({'name': name, 'passed': True, **fields})

groups = [
    ('authoring', 'authoring/manifest.json', 'sources'),
    ('execution', 'execution/source-manifest.json', None),
    ('interop', 'interop/source-manifest.json', 'files'),
]
for group, filename, key in groups:
    manifest = json.loads((ROOT / filename).read_text())
    rows = manifest[key] if key else manifest
    for row in rows:
        revision = row.get('revision', row.get('commit'))
        snapshot = Path(row.get('snapshot', row.get('copy')))
        raw = subprocess.check_output(['git', '-C', str(REPO), 'show', f"{revision}:{row['path']}"])
        saved = snapshot.read_bytes()
        record('frozen-source', raw == saved and sha(raw) == row['sha256'] and len(raw) == row['bytes'],
               group=group, path=row['path'], revision=revision, sha256=sha(raw))

models = [('authoring/probe.py', 'authoring/probe-results.json', 'passed'),
          ('execution/finite_controls.py', 'execution/finite-results.json', 'checks')]
model_results = []
for script, result, count_key in models:
    before = (ROOT / result).read_bytes()
    run = subprocess.run([sys.executable, str(ROOT / script)], text=True, capture_output=True)
    record('independent-python-model', run.returncode == 0 and before == (ROOT / result).read_bytes(),
           script=script, result=result, stdout=run.stdout.strip())
    data = json.loads(before)
    count = data[count_key]
    record('model-results-all-pass', all(row.get('pass', row.get('passed')) is True for row in data['results']),
           result=result, count=count)
    model_results.append({'script': script, 'checks': count, 'result_sha256': sha(before)})

rev = '4b57609c03ad0a38fd81cfc2c09ea5731dfe7ff0'
registry = subprocess.check_output(['git', '-C', str(REPO), 'show', rev + ':tools/Tools/SemanticsRegistry.lean']).decode()
start = registry.index('    { id := "R1", title :=')
end = registry.index('\n  ]\n  planScope', start)
block = registry[start:end] + '\n'
record('full-requirement-source', (ROOT / 'requirements-source.txt').read_text() == block,
       revision=rev, sha256=sha(block.encode()))
for n in range(1, 14):
    marker = f'{{ id := "R{n}", title :='
    part = block.split(marker, 1)[1]
    if n < 13:
        part = part.split(f'{{ id := "R{n+1}", title :=', 1)[0]
    record('requirement-open-parts', block.count(marker) == 1 and 'openParts := [' in part, requirement=f'R{n}')

papers = REPO / 'vendor/papers/program-graphs'
manifest = json.loads((papers / 'manifest.json').read_text())
for row in manifest['papers']:
    saved = (papers / row['file']).read_bytes()
    downloaded = (ROOT / 'papers' / row['file']).read_bytes()
    record('vendored-pdf-bytes', saved == downloaded and sha(saved) == row['sha256'] and len(saved) == row['bytes'],
           file=row['file'], sha256=sha(saved))
    info = subprocess.check_output(['pdfinfo', str(papers / row['file'])], text=True)
    pages = int(next(line.split(':', 1)[1] for line in info.splitlines() if line.startswith('Pages:')))
    record('pdf-page-count', pages == row['pdf_pages'], file=row['file'], pages=pages)
    for view in row['visual_reading']:
        record('figure-page-in-document', all(1 <= p <= pages for p in view['pdf_pages']), file=row['file'], pages=view['pdf_pages'])

hash_check = subprocess.run(['shasum', '-a', '256', '-c', 'SHA256SUMS'], cwd=papers, text=True, capture_output=True)
record('standalone-paper-hash-check', hash_check.returncode == 0, stdout=hash_check.stdout.strip())

language = subprocess.run([sys.executable, str(REPO / 'scripts/check-language.py'), '--show',
                          'vendor/papers/program-graphs/README.md',
                          'vendor/papers/program-graphs/citations-audit.md'], cwd=REPO, text=True, capture_output=True)
record('paper-guide-language', language.returncode == 0 and language.stdout == '' and language.stderr == '')

for file in ['recommendations.md', 'requirements.md', 'authoring/report.md', 'authoring/contracts.md',
             'execution/report.md', 'execution/api-data-proposal.json', 'interop/report.md',
             'interop/envelopes.txt', 'interop/obligations.json']:
    record('required-artifact', (ROOT / file).is_file() and (ROOT / file).stat().st_size > 0, file=file)

result = {'scope': 'Frozen source, paper bytes, document metadata and independent finite Python models. No Lean, compiler, Effect runtime, project build or generator.',
          'source_comparisons': sum(x['name'] == 'frozen-source' for x in checks),
          'comparisons': len(checks), 'all_passed': True, 'models': model_results, 'checks': checks}
(ROOT / 'parent-verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ['source_comparisons', 'comparisons', 'all_passed', 'models']}))
