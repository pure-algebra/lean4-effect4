import hashlib, json, os, pathlib, subprocess, time
p = pathlib.Path(__file__).resolve().parent
impl = pathlib.Path('/Users/pooks/Dev/lean4-effect4-wt/module-layers')
review = p.parents[2]
for module in ['ProofGraph', 'Tools/Graph']:
    destination = p / '.audit-lib' / module
    if not destination.exists():
        destination.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['cp', '-c', '-R', str(review / '.lake/build/lib/lean' / module),
                        str(destination)], check=True)
os.environ['LEAN_NUM_THREADS'] = '3'
os.environ['LEAN_PATH'] = str(p) + ':' + str(p / '.audit-lib') + ':' + str(impl / '.lake/build/lib/lean') + ':' + os.environ['LEAN_PATH']
command = ['lean', '-M6144', '-DwarningAsError=true', str(p / 'Audit.lean')]
t0 = time.monotonic()
r = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(p / 'audit.out').write_text(r.stdout)
record = {'command': command, 'exit': r.returncode, 'seconds': round(time.monotonic() - t0, 3),
          'module_sha256': hashlib.sha256((p / 'Probe.olean').read_bytes()).hexdigest()}
(p / 'audit-result.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record), flush=True)
print(r.stdout, flush=True)
raise SystemExit(r.returncode)
