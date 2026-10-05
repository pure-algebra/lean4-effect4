from urllib.request import urlopen, Request
from pathlib import Path
import json, hashlib, datetime, subprocess
r = Path(__file__).parent
sources = [
    ('handlers-in-scope-2014.pdf', 'https://people.cs.kuleuven.be/~tom.schrijvers/Research/papers/haskell2014.pdf'),
    ('scoped-effects-esop2024.pdf', 'https://www.cs.ox.ac.uk/people/samuel.staton/papers/esop2024.pdf'),
]
records = []
for name, url in sources:
    d = dict(url=url, file=name, retrieved_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    try:
        with urlopen(Request(url, headers={'User-Agent': 'Effect4-design-review/1.0'}), timeout=30) as h:
            b = h.read()
            d.update(status=h.status, final_url=h.url, content_type=h.headers.get('content-type'), bytes=len(b), sha256=hashlib.sha256(b).hexdigest())
        (r/name).write_bytes(b)
        p = subprocess.run(['/opt/homebrew/bin/pdftotext', '-layout', str(r/name), str(r/(name+'.txt'))], capture_output=True, text=True)
        d.update(extract_exit=p.returncode, extract_stderr=p.stderr)
    except Exception as e:
        d['error'] = str(e)
    records.append(d)
(r/'downloads.json').write_text(json.dumps(records, indent=2)+'\n')
print(json.dumps(records, indent=2))
