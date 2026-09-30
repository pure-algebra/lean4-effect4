"""Check this research packet's retained evidence and current constructor coverage."""
import hashlib
import json
import re
from pathlib import Path

folder = Path(__file__).resolve().parent
root = folder.parents[2]
document = folder.with_suffix('.md')
text = document.read_text()
ty_source = (root / 'src/Effect4/Program/Ty.lean').read_text()
ty_body = ty_source.split('inductive Ty', 1)[1].split('deriving DecidableEq', 1)[0]
constructors = re.findall(r'^  \| (\w+)', ty_body, re.M)
matrix = text.split('### Constructor-indexed acceptance matrix', 1)[1].split(
    'Both `Completion` constructors', 1)[0]
rows = re.findall(r'^\| `(\w+)` \|', matrix, re.M)
assert sorted(rows) == sorted(constructors), (rows, constructors)

for link in re.findall(r'\]\(([^)]+)\)', text):
    if '://' not in link and not link.startswith('#'):
        assert (document.parent / link.split('#')[0]).exists(), link

for path in folder.glob('*.lean'):
    assert not re.search(
        r'\b(sorry|native_decide|unsafe|partial|axiom|extern|implemented_by)\b',
        path.read_text()), path

for name in ('probe.log', 'predicate-probe.log'):
    output = (folder / name).read_text()
    assert 'error:' not in output and 'sorryAx' not in output
    assert 'Classical.choice' not in output
assert '11 finite guards passed.' in (folder / 'probe.log').read_text()
assert (folder / 'predicate-probe.log').read_text().count('depends on axioms:') == 5

manifest = json.loads((folder / 'sha256.json').read_text())
for relative, expected in manifest.items():
    actual = hashlib.sha256((root / relative).read_bytes()).hexdigest()
    assert actual == expected, relative
print(f'PASS: all {len(constructors)} Ty constructors covered; links, probe outputs and hashes agree')
