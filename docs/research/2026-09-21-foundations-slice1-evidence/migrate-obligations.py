from pathlib import Path
import re
rows = []
for base in ('src', 'Test'):
    for path in sorted(Path(base).rglob('*.lean')):
        source = path.read_text()
        starts = list(re.finditer(r'(?m)^(?:noncomputable )?(?:def|theorem|abbrev|end|namespace)\b', source))
        edits = []
        for i, match in enumerate(starts):
            block = source[match.start():starts[i + 1].start() if i + 1 < len(starts) else len(source)]
            if match[0] == 'def' and re.search(r':\s*(?:ProofGraph\.)?Obligation\b', block):
                assert ':= ⟨⟩' in block, (path, block[:100])
                rows.append((str(path), re.match(r'def\s+(\S+)', block)[1]))
                edits.append(match.start())
        for start in reversed(edits):
            source = source[:start] + 'theorem' + source[start + 3:]
        if edits:
            path.write_text(source)
Path('docs/research/2026-09-21-foundations-slice1-evidence/migration-inventory.tsv').write_text(
    ''.join(path + '\t' + name + '\n' for path, name in rows))
print(f'{len(rows)} declarations in {len({path for path, _ in rows})} files')
