"""Audit compiled draft laws without building in the implementation worktree."""
import datetime, hashlib, json, os, pathlib, re, subprocess, time
packet = pathlib.Path(__file__).resolve().parent
review = packet.parents[2]
impl = pathlib.Path('/Users/pooks/Dev/lean4-effect4-wt/module-layers')
cache = packet / '.audit-lib'
for name in ['ProofGraph', 'Tools/Graph']:
    target = cache / name
    if not target.exists():
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['cp', '-c', '-R', str(review / '.lake/build/lib/lean' / name), str(target)], check=True)
audit = packet / 'Effect4/Review/ModuleLayerAudit.lean'
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def closure():
    todo = re.findall(r'^import ([A-Za-z0-9_.]+)', audit.read_text(), re.M)
    found = {}
    while todo:
        name = todo.pop()
        if name in found:
            continue
        rel = pathlib.Path(*name.split('.')).with_suffix('.lean')
        root = impl if name.startswith('Effect4.') else review
        source = next((root / base / rel for base in ['src', 'tools', '.']
                       if (root / base / rel).is_file()), None)
        if source is None:
            continue
        found[name] = (root, source)
        todo.extend(re.findall(r'^(?:public )?import (?:all )?([A-Za-z0-9_.]+)', source.read_text(), re.M))
    return found
sources = closure()
def snapshot():
    result = {}
    for name, (root, source) in sources.items():
        result[str(source)] = sha(source)
        library = impl / '.lake/build/lib/lean' if name.startswith('Effect4.') else cache
        stem = library / pathlib.Path(*name.split('.'))
        for suffix in ['.olean', '.olean.private', '.olean.server', '.ir']:
            artifact = pathlib.Path(str(stem) + suffix)
            if artifact.exists():
                result[str(artifact)] = sha(artifact)
    return result
os.environ['LEAN_NUM_THREADS'] = '3'
os.environ['LEAN_PATH'] = str(cache) + ':' + str(impl / '.lake/build/lib/lean') + ':' + os.environ['LEAN_PATH']
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
before = snapshot()
(packet / 'inputs-before.json').write_text(json.dumps(before, indent=2) + '\n')
command = ['lean', '--root=' + str(packet), '-M6144', '-DwarningAsError=true', str(audit)]
t0 = time.monotonic()
result = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(packet / 'audit.out').write_text(result.stdout)
after = snapshot()
(packet / 'inputs-after.json').write_text(json.dumps(after, indent=2) + '\n')
changed = [name for name in sorted(before.keys() | after.keys()) if before.get(name) != after.get(name)]
record = {'started': started, 'implementation_base': subprocess.check_output(['git','-C',str(impl),'rev-parse','HEAD'],text=True).strip(),
          'review_parent': subprocess.check_output(['git','-C',str(review),'rev-parse','HEAD'],text=True).strip(),
          'command': command, 'working_directory': str(review),
          'lean_version': subprocess.check_output(['lean','--version'],text=True).strip(),
          'lean_path': os.environ['LEAN_PATH'], 'exit': result.returncode,
          'seconds': round(time.monotonic()-t0,3), 'source_modules': len(sources), 'inputs': len(before),
          'changed_inputs': changed, 'audit_sha256': sha(audit), 'output_sha256': sha(packet / 'audit.out')}
(packet / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2), flush=True)
print(result.stdout, flush=True)
raise SystemExit(result.returncode or (1 if changed else 0))
