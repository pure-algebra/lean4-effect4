from pathlib import Path
import hashlib
import json

folder = Path(__file__).resolve().parent
repo = folder.parents[2]
source = repo / 'docs/research/2026-10-09-mcp-code-mode/ShapeSchemaProbe.lean'
raw = source.read_bytes()
# Reuse the reviewed probe's declarations exactly; omit its top-level evaluations.
marker = '\nend ProbeMcp\n'
prefix = raw.decode().split(marker, 1)[0] + marker
result = ('import Effect4.Store.Domain.RowCanonical\n' + prefix +
          (folder / 'schema-controls-tail.lean').read_text())
(folder / 'SchemaControls.lean').write_text(result)
manifest = {
    'designCommit': 'c4b6b795638399fcbd6026630c05afb8bd75b268',
    'reviewedCommit': '28ed6727e1979b544a4d9c619cc837509511c0b6',
    'source': str(source.relative_to(repo)),
    'sourceSha256': hashlib.sha256(raw).hexdigest(),
    'copiedDeclarationsSha256': hashlib.sha256(prefix.encode()).hexdigest(),
    'generatedSha256': hashlib.sha256(result.encode()).hexdigest(),
}
(folder / 'schema-source.json').write_text(json.dumps(manifest, indent=2) + '\n')
print('Prepared SchemaControls.lean from the pinned probe and independent controls')
