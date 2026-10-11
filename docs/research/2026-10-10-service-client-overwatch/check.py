from pathlib import Path
import copy, hashlib, json, os, shutil, subprocess, tempfile

ROOT = Path(__file__).resolve().parents[3]
RECEIPT = Path(__file__).resolve().parent
PRIMARY = Path('/Users/pooks/Dev/lean4-effect4')
COMMIT = 'f6bf77246cd73e4d3b5206b239132fc4f0d037cd'
SNAPSHOT = RECEIPT / 'snapshot'
CHECKS = RECEIPT / 'checks'
CHECKS.mkdir(exist_ok=True)

def source(name):
    return subprocess.check_output(['git', 'show', COMMIT + ':' + name], cwd=PRIMARY)

def run(command, cwd, log):
    p = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=45,
                       env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1', 'GOMAXPROCS': '3'})
    (CHECKS / (log + '.log')).write_text(p.stdout)
    return p

paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', COMMIT], cwd=PRIMARY, text=True).splitlines()
files = ['Makefile', 'scripts/lean-imports.py', 'scripts/lib/lean_imports.py',
         'scripts/test-lean-imports.py', 'ts/eff/profile.gen.ts', 'ts/eff/eff.gen.ts']
files += [p for p in paths if p.startswith('harness/truth/') and Path(p).parent.as_posix() == 'harness/truth' and p.endswith('.ts')]
files += [p for p in paths if p.startswith('harness/truth/session/') and p.endswith('.ts')]
for name in files:
    dest = SNAPSHOT / name
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(source(name))
truth = SNAPSHOT / 'harness/truth'
node_modules = truth / 'node_modules'
if not node_modules.is_symlink():
    node_modules.symlink_to(PRIMARY / 'ts/eff/node_modules', target_is_directory=True)
(SNAPSHOT / 'node_modules').symlink_to(PRIMARY / 'ts/eff/node_modules', target_is_directory=True) if not (SNAPSHOT / 'node_modules').exists() else None

# Exact Makefile with source path inventory and controlled timestamps. No Lake executes.
with tempfile.TemporaryDirectory(prefix='make-', dir=CHECKS) as td:
    work = Path(td)
    selected = [p for p in paths if (p.startswith(('src/', 'Test/')) and p.endswith(('.lean', '.tsv'))) or p.startswith(('tools/Conform/', 'tools/Tools/', 'tools/Drivers/', 'tools/TestSupport/', 'tools/ProofGraph/')) or p in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'scripts/check-conform.py', 'scripts/lib/conform_report.py']]
    for name in selected:
        p = work / name; p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(b''); os.utime(p, (1000000000, 1000000000))
    (work / 'Makefile').write_bytes(source('Makefile'))
    for name in ['.lake/check/cases', '.lake/check/proof-style', '.lake/check/inventory', '.lake/build/lib/lean/Drivers/Corpus.trace', '.lake/corpus/index.tsv']:
        p = work / name; p.parent.mkdir(parents=True, exist_ok=True); p.write_text('existing\n')
        timestamp = 1150000000 if name.endswith('index.tsv') else 1100000000
        os.utime(p, (timestamp, timestamp))
    rows = []
    cases = [('unchanged', None), ('core_source', 'src/Effect4/Program/Authoring.lean'), ('toolchain_pin', 'lean-toolchain'), ('package_pin', 'lake-manifest.json'), ('lake_configuration', 'lakefile.toml')]
    for target, needle in [('check-cases', 'scripts/check-conform.py cases'), ('corpus', 'build Drivers.Corpus'), ('check-proof-style', 'env lean -DwarningAsError=true Test/Audit/ProofStyle.lean')]:
        for label, changed in cases:
            cmd = ['make', '-n', '-o', '.lake/check/inventory', target] + (['-W', changed] if changed else [])
            p = run(cmd, work, target + '-' + label)
            assert p.returncode == 0, (cmd, p.stdout)
            scheduled = needle in p.stdout
            expected_observed = changed is not None if target == 'check-cases' else label == 'core_source'
            assert scheduled == expected_observed, (target, label, p.stdout)
            rows.append({'target': target, 'case': label, 'command': cmd, 'exit_code': p.returncode, 'scheduled': scheduled, 'should_schedule': changed is not None})
    (work / 'PinsProbe.mk').write_text('.lake/build/lib/lean/Drivers/Corpus.trace .lake/check/proof-style: $(BUILD_PINS)\n')
    repairs = []
    for target, needle in [('corpus', 'build Drivers.Corpus'), ('check-proof-style', 'env lean -DwarningAsError=true Test/Audit/ProofStyle.lean')]:
        for label, changed in cases:
            cmd = ['make', '-n', '-o', '.lake/check/inventory', '-f', 'Makefile', '-f', 'PinsProbe.mk', target] + (['-W', changed] if changed else [])
            p = run(cmd, work, 'repair-' + target + '-' + label)
            assert p.returncode == 0 and (needle in p.stdout) == (changed is not None), (cmd, p.stdout)
            repairs.append({'target': target, 'case': label, 'scheduled': needle in p.stdout})
    (CHECKS / 'make-controls.json').write_text(json.dumps({'source_inventory_files': len(selected), 'method': 'Exact committed Makefile; empty source path mirror; fixed timestamps; unchanged inventory held old with -o; dry run only.', 'results': rows, 'local_prerequisite_repair': repairs}, indent=2) + '\n')

# Exercise the actual repaired Make helper with a harmless Lake substitute.
with tempfile.TemporaryDirectory(prefix='imports-', dir=CHECKS) as td:
    work = Path(td)
    for d in ['src', 'Test', 'tools/Conform', 'src/OCaml5/Lcnf', 'src/OCaml5/Ml', 'scripts/lib']:
        (work / d).mkdir(parents=True, exist_ok=True)
    for name in ['Makefile', 'scripts/lean-imports.py', 'scripts/lib/lean_imports.py', 'scripts/test-lean-imports.py']:
        (work / name).write_bytes(source(name))
    for name in ['src/Effect4/Api/HostProtocol.lean', 'src/Effect4/Program/Profile.lean', 'tools/Tools/GeneratedStamp.lean']:
        p = work / name; p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(b'')
    (work / 'ImportProbe.mk').write_text('probe:\n\t$(call build_imports,$(PROBE_FILE))\n')
    (work / 'lake-stub.py').write_text("import json,sys\nprint('CAPTURED_LAKE_ARGS='+json.dumps(sys.argv[1:]))\n")
    consumer = source('tools/Tools/HostProtocol.lean').decode()
    cases = [('current', consumer), ('leading_comment', '/- Ordinary header comment. -/\n' + consumer), ('between_imports', consumer.replace('import Lean.Data.Json', '/- Ordinary header comment. -/\nimport Lean.Data.Json')), ('empty_workspace_imports', 'import Lean\n'), ('missing_file', None)]
    rows = []
    for label, content in cases:
        fixture = work / (label + '.lean')
        if content is not None: fixture.write_text(content)
        cmd = ['make', '-s', '-f', 'Makefile', '-f', 'ImportProbe.mk', 'probe', 'LAKE=python3 ' + str(work / 'lake-stub.py'), 'PROBE_FILE=' + str(fixture)]
        p = run(cmd, work, 'imports-' + label)
        captured = [json.loads(line.split('=', 1)[1]) for line in p.stdout.splitlines() if line.startswith('CAPTURED_LAKE_ARGS=')]
        expected = [['build', 'Effect4.Api.HostProtocol', 'Effect4.Program.Profile', 'Tools.GeneratedStamp']] if label in ['current', 'leading_comment', 'between_imports'] else []
        assert captured == expected and (p.returncode != 0) == (label == 'missing_file'), (label, p.stdout)
        rows.append({'case': label, 'exit_code': p.returncode, 'captured_lake_args': captured, 'real_lake_executed': False})
    (work / 'src/Effect4/Program/Ty.lean').write_bytes(source('src/Effect4/Program/Ty.lean'))
    p = run(['python3', 'scripts/test-lean-imports.py'], work, 'shared-import-tests')
    assert p.returncode == 0, p.stdout
    (CHECKS / 'import-controls.json').write_text(json.dumps(rows, indent=2) + '\n')

# The exact landed Queue fixture through the exact landed runner, selected alone.
manifest = json.loads(source('harness/truth/corpus.json'))
entry = next(e for e in manifest['programs'] if e['name'] == 'pQueueService')
expected_exit = {'success': [True, 1]}
assert entry['run']['exit'] == entry['runSync']['exit'] == expected_exit
mutations = [('original', entry)]
wrong = copy.deepcopy(entry); wrong['client'] = 'export const client = Effect.succeed(tuple(false, 1))\n'; mutations.append(('wrong_value', wrong))
fail = copy.deepcopy(entry); fail['client'] = 'export const client = Effect.fail(42)\n'; mutations.append(('unexpected_failure', fail))
fresh = copy.deepcopy(entry)
assert fresh['decl'].count('take: () => queueTake(a0)') == 1
fresh['decl'] = fresh['decl'].replace('take: () => queueTake(a0)', 'take: () => Effect.flatMap(queueMake(), queueTake)')
mutations.append(('fresh_queue_for_take', fresh))
missing = copy.deepcopy(entry); missing['decl'] = None; missing['expr'] = None; mutations.append(('missing_module', missing))
mutations.append(('restored', entry))
compiler = PRIMARY / 'ts/eff/node_modules/.bin/tsgo'
version = run([str(compiler), '--version'], ROOT, 'tsgo-version').stdout.strip()
assert version == 'Version 7.0.0-dev.20260629.1', version
results = []
for label, variant in mutations:
    out = truth / 'controls' / label; out.mkdir(parents=True, exist_ok=True)
    for dependency in truth.glob('*.ts'):
        if not (out / dependency.name).is_symlink(): (out / dependency.name).symlink_to(dependency)
    if not (out / 'session').is_symlink(): (out / 'session').symlink_to(truth / 'session', target_is_directory=True)
    test_manifest = {**manifest, 'programs': [variant]}
    manifest_path = out / 'corpus.json'; manifest_path.write_text(json.dumps(test_manifest, indent=2) + '\n')
    cmd = ['bun', 'run', str(truth / 'run-truth.ts'), '--manifest', str(manifest_path), '--out', str(out), '--timeout', '100', '--only', 'pQueueService']
    p = run(cmd, ROOT, 'client-' + label)
    assert (out / 'result.json').exists(), (label, p.stdout)
    result = json.loads((out / 'result.json').read_text())
    row = result['rows'][0]
    assert len(result['rows']) == 1 and result['effect'] == '4.0.0-rc.112'
    should_pass = label in ['original', 'restored']
    observed_pass = label in ['original', 'restored', 'missing_module']
    assert (p.returncode == 0) == observed_pass, (label, p.stdout)
    if label != 'missing_module':
        assert row['clientAgree'] == should_pass and row['exitAgree'] and row['scheduleAgree'] and row['runSyncAgree'], row
        if should_pass: assert row['host']['exit'] == expected_exit
        generated = out / 'generated/pQueueService.ts'
        tscmd = [str(compiler), '--noEmit', '--strict', '--target', 'es2022', '--module', 'esnext', '--moduleResolution', 'bundler', '--allowImportingTsExtensions', '--skipLibCheck', str(generated)]
        typed = run(tscmd, ROOT, 'types-' + label)
        assert typed.returncode == 0, typed.stdout
        if should_pass:
            observation_path = out / 'client-observation.json'
            observe = ['bun', 'run', str(truth / 'run-truth.ts'), '--observe', str(generated), '--unit', 'client', '--result', str(observation_path), '--timeout', '100']
            q = run(observe, ROOT, 'client-observation-' + label)
            actual = json.loads(observation_path.read_text())
            assert q.returncode == 0 and actual['observation']['exit'] == expected_exit, actual
    else:
        assert 'clientAgree' not in row and row['host'] is None and row['exitAgree'] is None, row
    results.append({'case': label, 'command': cmd, 'exit_code': p.returncode, 'expected_pass': should_pass, 'summary': result['summary'], 'row': row})
(CHECKS / 'client-controls.json').write_text(json.dumps({'compiler': version, 'effect': '4.0.0-rc.112', 'method': 'Committed Lean output compared to fresh rc.112 execution; no Lean regeneration in this probe.', 'results': results}, indent=2) + '\n')
(RECEIPT / 'pins.json').write_text(json.dumps({'reviewed_commit': COMMIT, 'source_sha256': {name: hashlib.sha256(source(name)).hexdigest() for name in files + ['harness/truth/corpus.json']}, 'effect': json.loads((node_modules / 'effect/package.json').read_text())['version'], 'compiler': version}, indent=2) + '\n')
print(json.dumps({'import_controls': len(rows), 'service_client_controls': [{'case': x['case'], 'exit_code': x['exit_code'], 'clientAgree': x['row'].get('clientAgree')} for x in results], 'compiler': version}, indent=2))
