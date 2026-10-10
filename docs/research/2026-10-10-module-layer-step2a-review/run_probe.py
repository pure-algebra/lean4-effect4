"""Probe imported draft artifacts without running Lake in the implementation worktree."""
import datetime, hashlib, json, os, pathlib, re, subprocess, time
packet = pathlib.Path(__file__).resolve().parent
review = packet.parents[2]
impl = pathlib.Path('/Users/pooks/Dev/lean4-effect4-wt/module-layers')
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def git(*args):
    return subprocess.check_output(['git', '-C', str(impl), *args], text=True)
def closure():
    todo = ['Effect4.Program.Edit', 'Effect4.Api.HostSession']
    found = {}
    while todo:
        name = todo.pop()
        if name in found:
            continue
        rel = pathlib.Path(*name.split('.')).with_suffix('.lean')
        source = next((impl / base / rel for base in ['src', 'tools', '.']
                       if (impl / base / rel).is_file()), None)
        if source is None:
            continue
        found[name] = source
        for line in source.read_text().splitlines():
            match = re.match(r'^(?:public )?import (?:all )?([A-Za-z0-9_.]+)', line)
            if match:
                todo.append(match.group(1))
    return found
def snapshot():
    result = {}
    for name, source in closure().items():
        result[str(source.relative_to(impl))] = sha(source)
        stem = impl / '.lake/build/lib/lean' / pathlib.Path(*name.split('.'))
        for suffix in ['.olean', '.olean.private', '.olean.server', '.ir']:
            artifact = pathlib.Path(str(stem) + suffix)
            if artifact.exists():
                result[str(artifact.relative_to(impl))] = sha(artifact)
    return result
os.environ['LEAN_NUM_THREADS'] = '3'
os.environ['LEAN_PATH'] = str(impl / '.lake/build/lib/lean') + ':' + os.environ.get('LEAN_PATH', '')
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
before = snapshot()
(packet / 'draft.patch').write_text(git('diff', '--binary'))
(packet / 'inputs-before.json').write_text(json.dumps(before, indent=2) + '\n')
command = ['lean', '-M6144', '-DwarningAsError=true', '-o', str(packet / 'Probe.olean'), str(packet / 'Probe.lean')]
t0 = time.monotonic()
result = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(packet / 'probe.out').write_text(result.stdout)
after = snapshot()
(packet / 'inputs-after.json').write_text(json.dumps(after, indent=2) + '\n')
changed = [p for p in sorted(set(before) | set(after)) if before.get(p) != after.get(p)]
record = {'started': started, 'implementation_base': git('rev-parse', 'HEAD').strip(),
          'command': command, 'working_directory': str(review),
          'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
          'lean_path': os.environ['LEAN_PATH'], 'exit': result.returncode,
          'seconds': round(time.monotonic() - t0, 3), 'inputs': len(before),
          'changed_inputs': changed, 'probe_sha256': sha(packet / 'Probe.lean'),
          'output_sha256': sha(packet / 'probe.out'), 'draft_sha256': sha(packet / 'draft.patch')}
(packet / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2), flush=True)
print(result.stdout, flush=True)
raise SystemExit(result.returncode or (1 if changed else 0))
