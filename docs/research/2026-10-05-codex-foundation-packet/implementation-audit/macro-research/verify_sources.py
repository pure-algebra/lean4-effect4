"""Bounded read-only text checks. This invokes no compiler or generator."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import re
import subprocess

ROOT = Path('/Users/pooks/Dev/lean4-effect4')
OUT = Path('/private/tmp/codex-effect4-overnight-monitor/2026-10-06-macro-research')
REV = '33a1852942deaaa9c45a87a8a7e7b380b028043d'

def blob(path):
    return subprocess.check_output(['git', 'show', f'{REV}:{path}'], cwd=ROOT)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def parse_manifest(text):
    result = {}
    for line in text.splitlines():
        digest, path = line.split('  ', 1)
        if not re.fullmatch('[0-9a-f]{64}', digest):
            raise ValueError('digest')
        p = PurePosixPath(path)
        if p.is_absolute() or '..' in p.parts or not path.startswith('src/'):
            raise ValueError('path')
        if path in result:
            raise ValueError('duplicate')
        result[path] = digest
    return result

paths = '''AGENTS.md
docs/STATE.md
docs/ARCHITECTURE.md
docs/GENERATED.md
docs/core/decisions.md
docs/core/semantics.md
docs/core/controlled-english.md
docs/research/2026-10-05-claude-lead/migration-plan.md
src/Effect4/Program/Authoring.lean
src/Effect4/Program/Authoring/Sugar.lean
src/Effect4/Program/Authoring/Folds.lean
src/Effect4/Program/Authoring/Rows.lean
src/Effect4/Program/Authoring/Records.lean
src/Effect4/Program/Authoring/Services.lean
src/Effect4/Program/Record.lean
src/Effect4/Machine/Record.lean
src/Effect4/Api/Author.lean
src/Effect4/Codegen/Forms.lean
src/Effect4/Laws/Program/Author.lean
src/Effect4/Laws/Program/Authoring.lean
src/Effect4/Laws/Program/Authoring/Folds.lean
src/Effect4/Laws/Program/Authoring/Records.lean
src/Effect4/Laws/Codegen/Record.lean
src/Effect4/Program/Packages.lean
src/Effect4/Program/Packages/KeyValueStoreMemory.lean
src/Effect4/Program/Packages/SqliteBun.lean
src/OCaml5/Lcnf/Builtins.lean
tools/Effect4Gen/Rows.lean
tools/Effect4Gen/Forms.lean
tools/Effect4Gen/Atoms.lean
tools/Effect4Gen/PreludeAtoms.lean
tools/Effect4Gen/manifest.json
tools/Tools/Variances.lean
tools/Tools/GeneratedStamp.lean
tools/Tools/SemanticsRegistry.lean
tools/Drivers/TsGen.lean
Test/Dogfood/P4RateLimiter.lean
Test/Dogfood/P5LedgerService.lean
Test/Dogfood/P2HandlerLayers.lean
Test/Dogfood/Scenario/Atomic.lean
Test/Codegen/TermRows.lean
harness/truth/Truth.lean
harness/truth/prelude.ts
scripts/generate-effect-runtime-census.sh
scripts/check-truth-release.py
scripts/lib/truth_host.py
vendor/effect-4.0.0-rc.112/README.md
vendor/effect-4.0.0-rc.112/SHA256SUMS
vendor/effect-4.0.1/README.md
vendor/effect-4.0.1/SHA256SUMS
vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts
lake-manifest.json'''.splitlines()

sources = []
for path in paths:
    data = blob(path)
    sources.append({'path': str(ROOT / path), 'git_path': path, 'revision': REV,
                    'sha256': sha(data), 'bytes': len(data),
                    'current_equals_snapshot': (ROOT / path).read_bytes() == data})

package_rev = 'f5878bf879bd5712db964c2cd12802748c707605'
for path in ['README.md', 'TypeScript/Syntax.lean', 'TypeScript/TypeRef.lean']:
    full = ROOT / '.lake/packages/typescript' / path
    data = full.read_bytes()
    committed = subprocess.check_output(['git', 'show', f'{package_rev}:{path}'], cwd=full.parent if path == 'README.md' else full.parent.parent)
    sources.append({'path': str(full), 'revision': package_rev, 'sha256': sha(data),
                    'bytes': len(data), 'current_equals_snapshot': data == committed})

script = blob('scripts/generate-effect-runtime-census.sh').decode()
block = script.split("cat <<'INPUTS'\n", 1)[1].split('\nINPUTS', 1)[0]
manifest_text = blob('vendor/effect-4.0.0-rc.112/SHA256SUMS').decode()
manifest = parse_manifest(manifest_text)
checks = []
for line in block.splitlines():
    path, digest = line.split('|')
    source_path = 'vendor/effect-4.0.0-rc.112/src/' + path
    actual = sha(blob(source_path))
    assert manifest['src/' + path] == digest == actual
    checks.append({'check': 'census-manifest-source-equality', 'path': path, 'pass': True})

first = block.splitlines()[0]
path, expected = first.split('|')
mutant = ('0' if expected[0] != '0' else '1') + expected[1:]
assert mutant != manifest['src/' + path]
checks.append({'check': 'changed-digest-mutant-refused', 'pass': True})
for name, bad in [
    ('duplicate-path', manifest_text + manifest_text.splitlines()[0] + '\n'),
    ('path-escape', '0' * 64 + '  src/../outside\n'),
    ('invalid-digest', 'z' * 64 + '  src/X.ts\n')]:
    try:
        parse_manifest(bad)
    except ValueError:
        checks.append({'check': name + '-refused-by-research-parser', 'pass': True})
    else:
        raise AssertionError(name)

assert all(row['current_equals_snapshot'] for row in sources)
(OUT / 'sources.json').write_text(json.dumps({'revision': REV, 'sources': sources}, indent=2) + '\n')
(OUT / 'checks.json').write_text(json.dumps({'scope': 'read-only source identity and a research text parser; no compiler or generator', 'checks': checks}, indent=2) + '\n')
print(json.dumps({'source_hashes': len(sources), 'all_current_equal_snapshot': True,
                  'checks': len(checks), 'census_file_comparisons': len(block.splitlines())}))
