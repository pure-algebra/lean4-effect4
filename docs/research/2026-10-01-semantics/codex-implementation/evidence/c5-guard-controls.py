#!/usr/bin/env python3
"""Private finite orchestration controls. No Lean, Lake, compiler or live artifact writes."""
import ast
import contextlib
import io
import json
from pathlib import Path
import tempfile

SCRIPT = Path('/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4/scripts/check-semantics.py')
module = {'__file__': str(SCRIPT), '__name__': 'private_semantics_guard_controls'}
source = SCRIPT.read_text()
ast.parse(source)
exec(compile(source, str(SCRIPT), 'exec'), module)
passed = []


def check(label, operation):
    operation()
    passed.append(label)
    print('PASS ' + label)


def refuses(operation, fragment):
    try:
        operation()
    except RuntimeError as error:
        assert fragment in str(error), str(error)
    else:
        raise AssertionError('control accepted: ' + fragment)


with tempfile.TemporaryDirectory(prefix='semantics-c5-guards-') as temporary:
    root = Path(temporary)
    report = root / 'roots.json'
    report.write_text(json.dumps({'provenance': {'roots': list(module['TARGETS'][:2])}}))
    check('prepared report roots accepted', lambda: module['require_report_roots'](report))
    report.write_text(json.dumps({'provenance': {'roots': [module['TARGETS'][0], 'Effect4.Unprepared']}}))
    check('unprepared report root refused', lambda: refuses(lambda: module['require_report_roots'](report), 'Effect4.Unprepared'))

    module['ROOT'] = root
    module['TARGETS'] = ('Test.Root',)
    rootbase = root / module['TRACE_DIR'] / 'Test/Root'
    depbase = root / module['TRACE_DIR'] / 'Dep/Basic'

    def artifact(base, payload, parts=('olean',)):
        outputs = {'o': []}
        for suffix in parts:
            data = payload + suffix.encode()
            path = Path(str(base) + '.' + suffix)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            description = module['lake_binary_hash'](data) + '.' + suffix
            if suffix.startswith('olean'):
                outputs['o'].append(description)
            else:
                outputs['rs' if suffix == 'ir.sig' else 'r'] = description
        base.with_suffix('.trace').write_text(json.dumps({'outputs': outputs}))

    artifact(rootbase, b'root')
    artifact(depbase, b'dep', ('olean', 'olean.server', 'olean.private', 'ir.sig', 'ir'))
    setup = root / '.lake/build/ir/Test/Root.setup.json'
    setup.parent.mkdir(parents=True)
    setup.write_text(json.dumps({'name': 'Test.Root', 'importArts': {
        'Dep.Basic': [[str(depbase) + '.olean'], [str(depbase) + '.ir.sig', str(depbase) + '.ir']]}}))
    observed = {}
    check('saved root and import hashes accepted', lambda: module['verify_saved_outputs'](observed))
    assert len(observed['savedOutputs']) == 6
    Path(str(depbase) + '.olean.private').write_bytes(b'corrupt')
    check('corrupt imported private artifact refused', lambda: refuses(lambda: module['verify_saved_outputs']({}), 'saved-output hash mismatch'))
    artifact(depbase, b'dep', ('olean', 'olean.server', 'olean.private', 'ir.sig', 'ir'))
    Path(str(rootbase) + '.olean').write_bytes(b'corrupt root')
    check('corrupt dynamic root artifact refused', lambda: refuses(lambda: module['verify_saved_outputs']({}), 'saved-output hash mismatch'))
    artifact(rootbase, b'root')
    with Path(str(rootbase) + '.olean').open('r+b') as stream:
        stream.truncate(128 * 1024 * 1024 + 1)
    check('oversized artifact refused before reading', lambda: refuses(lambda: module['verify_saved_outputs']({}), '128 MiB'))
    artifact(rootbase, b'root')
    clock = module['time'].monotonic
    ticks = iter((0, 1000))
    module['time'].monotonic = lambda: next(ticks)
    try:
        check('hash traversal deadline refused', lambda: refuses(lambda: module['verify_saved_outputs']({}), '180 seconds'))
    finally:
        module['time'].monotonic = clock

    stage, out = root / 'stage', root / 'generated'
    stage.mkdir()
    out.mkdir()
    for name in module['FILES']:
        (stage / name).write_bytes(b'new')
        (out / name).write_bytes(b'old')
    original_replace = module['os'].replace
    calls = {'count': 0}

    def fail_second(source_path, destination):
        calls['count'] += 1
        if calls['count'] == 2:
            raise OSError('injected second-publication failure')
        return original_replace(source_path, destination)

    module['os'].replace = fail_second
    try:
        try:
            module['publish_reports'](stage, out)
        except OSError as error:
            assert 'injected' in str(error)
        else:
            raise AssertionError('partial publication accepted')
    finally:
        module['os'].replace = original_replace
    check('partial publication restores both prior files', lambda: None if all((out / name).read_bytes() == b'old' for name in module['FILES']) else (_ for _ in ()).throw(AssertionError('prior outputs changed')))
    module['publish_reports'](stage, out)
    assert all((out / name).read_bytes() == b'new' for name in module['FILES'])
    check('validated publication replaces both files', lambda: None)

    module['run'] = lambda *args, **kwargs: 'fixture-head'
    module['digest'] = lambda path: 'fixture-hash'
    module['sys'].argv = ['check-semantics.py', '--generate', 'generated']

    def fake_lean(file, receipt, *args):
        directory = Path(args[0])
        (directory / 'semantics.json').write_text(json.dumps({'provenance': {'roots': ['Test.Root']}}))
        (directory / 'semantics.md').write_bytes(b'new')

    module['lean'] = fake_lean
    for scenario in ('snapshot-change', 'late-freshness'):
        for name in module['FILES']:
            (out / name).write_bytes(b'old')
        count = {'snapshot': 0, 'freshness': 0}

        def snapshot():
            count['snapshot'] += 1
            return {'input': str(count['snapshot']) if scenario == 'snapshot-change' else 'same'}

        def freshness(receipt):
            count['freshness'] += 1
            if scenario == 'late-freshness' and count['freshness'] == 2:
                raise RuntimeError('injected final freshness refusal')

        module['snapshot'] = snapshot
        module['require_artifacts'] = freshness
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            assert module['main']() == 1
        assert all((out / name).read_bytes() == b'old' for name in module['FILES'])
        receipt = json.loads((root / '.lake/gen/semantics.receipt.json').read_text())
        assert receipt['result'] == 'failed'
        check(scenario + ' preserves both prior files', lambda: None)

assert '"GOMAXPROCS": "1"' in source and '"GOMEMLIMIT": "512MiB"' in source
check('host process and memory bounds present', lambda: None)
print(f'PASS C5 guard controls: {len(passed)} finite controls; no compiler or live artifact mutation')
