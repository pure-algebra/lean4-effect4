import ast
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from unittest.mock import patch

source = Path('/Users/pooks/Dev/lean4-effect4/scripts/status.py')
body = source.read_text()
parsed = ast.parse(body)
function = next(n for n in parsed.body if isinstance(n, ast.FunctionDef) and n.name == 'lake_cache')
namespace = dict(os=os, Path=Path, subprocess=subprocess, ROOT=source.parent.parent)
exec(compile(ast.Module(body=[function], type_ignores=[]), str(source), 'exec'), namespace)
probe = namespace['lake_cache']
results = []
empty_path = Path(__file__).parent / 'empty-path'
empty_path.mkdir(exist_ok=True)
base = {'PATH': str(empty_path), 'XDG_CACHE_HOME': '/test/cache'}
with patch.dict(os.environ, base, clear=True):
    try:
        probe()
        raise AssertionError('Expected absent-elan failure')
    except FileNotFoundError as e:
        assert e.filename == 'elan'
        results.append({'case': 'elan absent, no override', 'observation': 'FileNotFoundError', 'filename': e.filename})
with patch.dict(os.environ, {**base, 'LAKE_CACHE_DIR': '/test/explicit'}, clear=True):
    assert probe() == Path('/test/explicit')
    results.append({'case': 'explicit override', 'observation': '/test/explicit'})
with patch.dict(os.environ, {**base, 'LAKE_CACHE_DIR': ''}, clear=True):
    assert probe() is None
    results.append({'case': 'explicitly disabled', 'observation': None})
with patch.dict(os.environ, base, clear=True), patch.object(subprocess, 'run', return_value=subprocess.CompletedProcess(['elan', 'which', 'lake'], 1, '', 'no toolchain')):
    assert probe() == Path('/test/cache/lake')
    results.append({'case': 'elan present, command fails (mocked)', 'observation': '/test/cache/lake'})
with patch.dict(os.environ, base, clear=True), patch.object(subprocess, 'run', return_value=subprocess.CompletedProcess(['elan', 'which', 'lake'], 0, '/test/toolchain/bin/lake\n', '')):
    assert probe() == Path('/test/toolchain/lake/cache')
    results.append({'case': 'elan resolves toolchain (mocked)', 'observation': '/test/toolchain/lake/cache'})
receipt = {'python': sys.version, 'source': str(source), 'sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'method': 'AST-extracted actual lake_cache, isolated environment; no main/report/Lean run', 'results': results}
output = Path(__file__).parent / 'receipt.json'
output.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
