"""Compare one source-refusal observation on the base and the compiled draft."""
import datetime, hashlib, json, os, pathlib, subprocess, time
packet = pathlib.Path(__file__).resolve().parent
review = packet.parents[2]
draft = pathlib.Path('/Users/pooks/Dev/lean4-effect4-wt/module-layers')
initial_path = os.environ['LEAN_PATH']
os.environ['LEAN_NUM_THREADS'] = '3'
records = []
for name, root in [('DiagnosticBase', review), ('DiagnosticDraft', draft), ('RefusalOrderDraft', draft)]:
    env = dict(os.environ)
    env['LEAN_PATH'] = str(root / '.lake/build/lib/lean') + ':' + initial_path
    input_files = [root / 'src/Effect4/Program/Refs.lean', root / 'src/Effect4/Program/Eff.lean']
    for module in ['Effect4/Api', 'Effect4/Program/Refs', 'Effect4/Program/Eff']:
        for suffix in ['.olean', '.olean.private', '.olean.server', '.ir']:
            file = root / '.lake/build/lib/lean' / (module + suffix)
            if file.exists(): input_files.append(file)
    def hashes():
        return {str(file): hashlib.sha256(file.read_bytes()).hexdigest() for file in input_files}
    before = hashes()
    command = ['lean', '-M6144', '-DwarningAsError=true', str(packet / (name + '.lean'))]
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    t0 = time.monotonic()
    result = subprocess.run(command, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (packet / (name + '.out')).write_text(result.stdout)
    after = hashes()
    record = {'file':name + '.lean', 'command':command, 'started':started,
              'exit':result.returncode, 'seconds':round(time.monotonic()-t0,3),
              'head':subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip(),
              'before':before, 'after':after, 'stable':before == after}
    records.append(record)
    print(name, result.returncode, result.stdout, flush=True)
    if result.returncode or before != after: break
(packet / 'diagnostic-results.json').write_text(json.dumps(records,indent=2) + '\n')
raise SystemExit(0 if len(records) == 3 and all(r['exit'] == 0 and r['stable'] for r in records) else 1)
