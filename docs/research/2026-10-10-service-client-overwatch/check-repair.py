from pathlib import Path
import difflib, json, os, subprocess
r = Path(__file__).resolve().parent
root = r.parents[2]
truth = r / 'snapshot/harness/truth'
original = (truth / 'run-truth.ts').read_text()
anchor = '        notes: [`printer refused: ${entry.exprRefusal}`], host: null, hostSync: null\n'
assert original.count(anchor) == 1
repaired = original.replace(anchor, '        ...(entry.client === undefined ? {} : { clientAgree: false }),\n' + anchor)
runner = truth / 'run-truth-repaired.ts'
runner.write_text(repaired)
(r / 'runner-repair.patch').write_text(''.join(difflib.unified_diff(original.splitlines(keepends=True), repaired.splitlines(keepends=True), fromfile='a/harness/truth/run-truth.ts', tofile='b/harness/truth/run-truth.ts')))
rows = []
for label in ['original', 'missing_module', 'unexpected_failure']:
    manifest = truth / 'controls' / label / 'corpus.json'
    out = truth / 'repair-controls' / label
    out.mkdir(parents=True, exist_ok=True)
    for dependency in truth.glob('*.ts'):
        if not (out / dependency.name).is_symlink(): (out / dependency.name).symlink_to(dependency)
    if not (out / 'session').is_symlink(): (out / 'session').symlink_to(truth / 'session', target_is_directory=True)
    command = ['bun', 'run', str(runner), '--manifest', str(manifest), '--out', str(out), '--timeout', '100', '--only', 'pQueueService']
    p = subprocess.run(command, cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
    (r / 'checks' / ('repair-client-' + label + '.log')).write_text(p.stdout)
    result = json.loads((out / 'result.json').read_text())
    wanted = label == 'original'
    assert (p.returncode == 0) == wanted and result['rows'][0]['clientAgree'] == wanted, (label, p.stdout)
    rows.append({'case': label, 'command': command, 'exit_code': p.returncode, 'clientAgree': result['rows'][0]['clientAgree']})
compiler = root / 'ts/eff/node_modules/.bin/tsgo'
command = [str(compiler), '--noEmit', '--strict', '--target', 'es2022', '--module', 'esnext', '--moduleResolution', 'bundler', '--allowImportingTsExtensions', '--skipLibCheck', '--types', 'bun', '--typeRoots', str(root / 'ts/eff/node_modules/@types'), str(runner)]
p = subprocess.run(command, cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=45, env={**os.environ, 'GOMAXPROCS':'3'})
(r / 'checks/repair-runner-types.log').write_text(p.stdout)
assert p.returncode == 0, p.stdout
(r / 'checks/repair-client-controls.json').write_text(json.dumps({'results': rows, 'compiler_command': command, 'compiler_exit': p.returncode}, indent=2) + '\n')
print(json.dumps(rows, indent=2))
