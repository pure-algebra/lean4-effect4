from pathlib import Path
from datetime import datetime, timezone
import json, hashlib, re

r = Path(__file__).parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifests = [
    'literature/stm/downloads.json',
    'literature/tasks/resources/manifest.json',
    'literature/clocks/download-manifest.json',
    'literature/scopes/downloads.json',
    'literature/refinement/downloads.json',
]
checked, unavailable = [], []
for name in manifests:
    manifest = r/name
    data = json.loads(manifest.read_text())
    for item in (data if isinstance(data, list) else [data]):
        if 'error' in item:
            unavailable.append(dict(manifest=name, url=item['url'], reason=item['error']))
            continue
        file = Path(item['path']) if 'path' in item else manifest.parent/item.get('file', item.get('name'))
        assert file.exists(), file
        assert sha(file) == item['sha256'], file
        if 'bytes' in item:
            assert file.stat().st_size == item['bytes'], file
        checked.append(dict(file=str(file.relative_to(r)), sha256=sha(file), url=item['url']))
for item in json.loads((r/'atomic/cancel-return/receipt.json').read_text())['files']:
    assert sha(Path(item['path'])) == item['sha256'], item
versions = []
for version in ['rc112', 'v401']:
    data = json.loads((r/f'atomic/cancel-return/{version}.json').read_text())
    assert [c['target']['tag'] for c in data['cases']] == ['Success', 'Failure', 'Failure', 'Failure']
    assert [any(e['event']=='caller-continuation-entered' for e in c['events']) for c in data['cases']] == [True, False, False, True]
    assert all(c['queueSize']==0 and c['tasksExecuted']==0 for c in data['cases'])
    assert data['precommitControl']['laterPoll'] == {'tag':'Some', 'value':'retained-message'}
    versions.append(data['runtime'])
docs = ['contracts-and-literature.md', 'review.md', 'foundation-audit.md', 'literature/stm/contract-findings.md', 'literature/tasks/contracts.md', 'literature/clocks/review.md', 'literature/scopes/review.md']
links = []
for name in docs:
    for link in re.findall(r'\]\(([^)]+)\)', (r/name).read_text()):
        if link.startswith(('https:', 'http:')):
            continue
        p = Path(link) if link.startswith('/') else (r/name).parent/link
        assert p.exists(), (name, link)
        links.append(dict(document=name, link=link))
result = dict(verified_at_utc=datetime.now(timezone.utc).isoformat(), command=f'python3 {r}/verify-literature.py', downloads_verified=checked, unavailable_downloads=unavailable, cancellation_cases_checked=10, cancellation_runtime_versions=versions, local_links_checked=len(links), report_hashes={name:sha(r/name) for name in docs}, limits=['Sources inform design; no imported theorem is a project proof', 'Downloaded source files were not executed', 'Cancellation probes are finite host evidence'])
(r/'literature-verification.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(dict(verified=True, downloads=len(checked), unavailable=len(unavailable), cancellation_cases=10, local_links=len(links))))
