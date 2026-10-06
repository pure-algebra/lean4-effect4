import concurrent.futures
import hashlib
import json
import subprocess
import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCES = [
    ('bidirectional-type-slicing-2607.12197v1.pdf', 'https://arxiv.org/pdf/2607.12197v1'),
    ('lamport-1978-time-clocks.pdf', 'https://lamport.azurewebsites.net/pubs/time-clocks.pdf'),
    ('huet-zipper.pdf', 'https://gallium.inria.fr/~huet/PUBLIC/zip.pdf'),
    ('allais-binding-universe.pdf', 'https://bentnib.org/binding-universe.pdf'),
    ('hazelnut-1607.04180v5.pdf', 'https://arxiv.org/pdf/1607.04180v5'),
    ('foster-bidirectional-tree-transformations.pdf', 'https://www.cis.upenn.edu/~bcpierce/papers/newlenses-full.pdf'),
    ('interaction-trees-author.pdf', 'https://perso.ens-lyon.fr/yannick.zakowski/papers/itrees.pdf'),
    ('choice-trees-2211.06863.pdf', 'https://arxiv.org/pdf/2211.06863'),
    ('tristan-leroy-2008-validation-scheduling.pdf', 'https://xavierleroy.org/publi/validation-scheduling.pdf'),
]

def fetch(row):
    name, url = row
    out = ROOT / name
    result = subprocess.run(['curl', '--fail', '--location', '--silent', '--show-error',
                             '--connect-timeout', '15', '--max-time', '60',
                             '--output', str(out), '--write-out', '%{url_effective}', url],
                            capture_output=True, text=True)
    if result.returncode:
        return {'file': name, 'source_url': url, 'status': 'failed', 'error': result.stderr.strip()}
    data = out.read_bytes()
    if not data.startswith(b'%PDF-'):
        return {'file': name, 'source_url': url, 'status': 'refused_non_pdf', 'bytes': len(data)}
    info = subprocess.run(['pdfinfo', str(out)], capture_output=True, text=True)
    if info.returncode:
        return {'file': name, 'source_url': url, 'status': 'refused_pdfinfo', 'error': info.stderr}
    text = subprocess.run(['pdftotext', '-layout', str(out), str(out.with_suffix('.txt'))],
                          capture_output=True, text=True)
    if text.returncode:
        return {'file': name, 'source_url': url, 'status': 'refused_text', 'error': text.stderr}
    out.with_suffix('.pdfinfo.txt').write_text(info.stdout)
    return {'file': name, 'source_url': url, 'resolved_url': result.stdout,
            'status': 'downloaded_valid_pdf', 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest(),
            'accessed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}

with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
    results = list(pool.map(fetch, SOURCES))
(ROOT / 'downloads.json').write_text(json.dumps(results, indent=2) + '\n')
for row in results:
    print(json.dumps(row))
if any(row['status'] != 'downloaded_valid_pdf' for row in results):
    raise SystemExit(1)
