"""Bounded prerequisite test using the source semantics rule and a fake Lake driver."""
from pathlib import Path
import hashlib
import os
import subprocess
import tempfile
import sys
import importlib.util

repo = Path(sys.argv[1]).resolve()
sys.dont_write_bytecode = True
source = (repo / 'Makefile').read_text()
rule = source[source.index('SEMANTICS_SOURCES :='):source.index('# The groups generate.py')]
inputs_text = rule[:rule.index('$(GEN)/semantics:')].replace('\\\n', ' ')
inputs = inputs_text.split(':=', 1)[1].split()
with tempfile.TemporaryDirectory(prefix='effect4-marker-fixture-', dir='/private/tmp') as directory:
    root = Path(directory)
    def put(name, value='', stamp=100):
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value)
        os.utime(path, (stamp, stamp))
    put('fake_lake.py', "from pathlib import Path\nimport sys\nwith Path('calls').open('a') as f: f.write(' '.join(sys.argv[1:])+'\\n')\nif sys.argv[1] == 'exe':\n p=Path(sys.argv[-1]); p.mkdir(parents=True,exist_ok=True); (p/'semantics.md').write_text('fresh')\n")
    put('Makefile', 'GEN := .lake/gen\nLAWS := .lake/build/lib/lean/Effect4/Laws.trace\nLAKE := python3 fake_lake.py\n.PHONY: build\nbuild:\n\t@:\n' + rule)
    for name in inputs + ['.lake/build/lib/lean/Effect4/Laws.trace']:
        put(name)
    put('.lake/gen/semantics', stamp=200)
    put('generated/semantics.md', 'old', stamp=200)
    def run():
        result = subprocess.run(['make', '.lake/gen/semantics'], cwd=root, capture_output=True, text=True)
        assert result.returncode == 0, result.stderr
        return (root / 'calls').read_text() if (root / 'calls').exists() else ''
    assert run() == ''
    put('.lake/build/lib/lean/Test/Program/TypedProgBindRed.trace', stamp=300)
    assert run() == '', 'test-root trace unexpectedly invalidates the marker'
    print('REPRODUCED: newer independent Test root trace does not regenerate report')
    (root / 'generated/semantics.md').unlink()
    assert run() == '', 'missing output unexpectedly invalidates the marker'
    assert not (root / 'generated/semantics.md').exists()
    print('REPRODUCED: missing report does not regenerate report')
    put('tools/Tools/SemanticsRegistry.lean', stamp=300)
    assert 'exe semantics-report' in run(), 'positive invalidation control failed'
    assert (root / 'generated/semantics.md').read_text() == 'fresh'
    print('PASS: newer declared registry input invokes fake producer and replaces report')
    print('Rule SHA256: ' + hashlib.sha256(rule.encode()).hexdigest())
    print('Scope: actual Make rule in isolated fixture; fake Lake only; no repository mutation or Lean execution')

# Run the real manifest function on representative files in an isolated directory.
spec = importlib.util.spec_from_file_location('foundation_conform_report', repo / 'scripts/lib/conform_report.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
with tempfile.TemporaryDirectory(prefix='effect4-manifest-fixture-', dir='/private/tmp') as directory:
    root = Path(directory)
    present = 'ocaml/engine/api_engine.ml'
    omitted = ['ocaml/gen/externs.txt', 'ocaml/engine/api_engine.mli', 'ocaml/engine/dune', 'ocaml/engine/closure.tsv']
    for name in [present] + omitted:
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('version one')
    before = module.manifest(root)
    assert present in before
    assert all(name not in before for name in omitted)
    for name in omitted:
        (root / name).write_text('version two')
        assert module.manifest(root) == before
    print('REPRODUCED: externs.txt, .mli, dune and .tsv changes are absent from Conform manifest')
    (root / present).write_text('version two')
    assert module.manifest(root) != before
    print('PASS: changed .ml file changes Conform manifest')
    print('Scope: production manifest function on isolated representative files; no target or Lean execution')
