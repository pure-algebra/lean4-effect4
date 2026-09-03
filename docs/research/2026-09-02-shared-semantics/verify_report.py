from pathlib import Path
import hashlib, json, re
from pypdf import PdfReader
import pdfplumber

bundle = Path(__file__).resolve().parent
root = bundle.parents[2]
pdf = root / 'output/pdf/effect4-web-standards-semantics.pdf'
source = bundle / 'report-source.md'
ledger = json.loads((bundle / 'source-ledger.json').read_text())
reader = PdfReader(pdf)
texts = [p.extract_text() for p in reader.pages]
all_text = '\n'.join(texts)
assert len(texts) == 15
assert len(reader.outline) == 14
assert all(len(t) > 200 for t in texts)
assert not any(x in all_text for x in ['\ufffd', 'TODO', 'TBD'])
for n in range(1, 11):
    assert re.search(r'\b' + str(n) + r'\. ', all_text)
uris, destinations = [], []
page_ids = {p.indirect_reference.idnum for p in reader.pages}
for page in reader.pages:
    for ref in page.get('/Annots', []):
        ann = ref.get_object()
        if ann.get('/A', {}).get('/URI'):
            uris.append(str(ann['/A']['/URI']))
        if ann.get('/Dest'):
            dest = ann['/Dest']
            assert dest[0].idnum in page_ids
            destinations.append(dest[0].idnum)
expected = {r['url'] for r in ledger['external']}
assert expected == set(uris)
with pdfplumber.open(pdf) as doc:
    for page in doc.pages:
        for ch in page.chars:
            assert 42 <= ch['x0'] <= ch['x1'] <= 553
            assert 15 <= ch['top'] <= ch['bottom'] <= 825
for item in ledger['local']:
    p = Path(item.get('root', '/')) / item['path']
    assert hashlib.sha256(p.read_bytes()).hexdigest() == item['sha256'], str(p)
axioms = (bundle / 'verification/frame-axiom-receipts.txt').read_text()
rows = [x for x in axioms.splitlines() if x.startswith("'")]
assert len(rows) == 149
used = set()
for row in rows:
    m = re.search(r'depends on axioms: \[([^\]]*)\]', row)
    if m: used.update(x.strip() for x in m[1].split(',') if x.strip())
assert used <= {'propext', 'Quot.sound'}, used
result = {
    'pdf': str(pdf),
    'pdf_sha256': hashlib.sha256(pdf.read_bytes()).hexdigest(),
    'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'pages': len(texts),
    'outline_sections': len(reader.outline),
    'unique_external_urls': len(expected),
    'external_link_annotations': len(uris),
    'resolved_internal_link_annotations': len(destinations),
    'all_page_text_and_margins_checked': True,
    'visually_inspected_pages': [1, 6, 8, 11, 12, 14, 15],
    'visual_review_scope': 'Sampled rendered pages. Page 15 re-rendered and re-inspected after final QA note; earlier sampled pages unchanged.',
    'local_source_hashes_rechecked': len(ledger['local']),
    'frame_axiom_receipts': len(rows),
    'frame_axioms_used': sorted(used),
    'limitations': 'Link annotations and cited source presence were checked; no claim that every external host will remain available. No accessibility tagging review.'
}
(bundle / 'verification/document-checks.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
