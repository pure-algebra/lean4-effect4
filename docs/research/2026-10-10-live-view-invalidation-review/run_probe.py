"""Build two pinned research modules and one finite probe in the isolated packet."""
import datetime, hashlib, json, os, pathlib, re, subprocess, time, sys
packet = pathlib.Path(__file__).resolve().parent
review = packet.parents[2]
primary = pathlib.Path('/Users/pooks/Dev/lean4-effect4')
revision = 'e9d6863eed613a40fe90444925daf5e3bec818c5'
cache = packet / 'build'
(cache / 'ProbeView').mkdir(parents=True, exist_ok=True)
os.environ['LEAN_NUM_THREADS'] = '3'
os.environ['LEAN_PATH'] = str(cache) + ':' + str(primary / '.lake/build/lib/lean') + ':' + os.environ['LEAN_PATH']

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def closure():
    todo = ['ProbeView.Inc']
    found = {}
    while todo:
        name = todo.pop()
        if name in found:
            continue
        rel = pathlib.Path(*name.split('.')).with_suffix('.lean')
        source = next((base / rel for base in [packet / 'src', primary / 'src', primary / 'tools', primary]
                       if (base / rel).is_file()), None)
        if source is None:
            continue
        if name.startswith('ProbeView.'):
            original = 'docs/research/2026-10-10-live-view/probes/src/' + str(rel)
        else:
            original = str(source.relative_to(primary))
        committed = subprocess.check_output(['git','show',revision+':'+original])
        assert hashlib.sha256(committed).hexdigest() == sha(source), str(source)
        found[name] = source
        todo.extend(re.findall(r'^(?:public )?import (?:all )?([A-Za-z0-9_.]+)', source.read_text(), re.M))
    return found
sources = closure()
def snapshot():
    result = {str(path): sha(path) for path in sources.values()}
    for name in sources:
        if name.startswith('ProbeView.'):
            continue
        stem = primary / '.lake/build/lib/lean' / pathlib.Path(*name.split('.'))
        for ext in ['.olean','.olean.private','.olean.server','.ir']:
            artifact = pathlib.Path(str(stem) + ext)
            if artifact.exists():
                result[str(artifact)] = sha(artifact)
    return result
probe_only = '--probe-only' in sys.argv
prefix = 'consumer-' if probe_only else ''
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
before = snapshot()
(packet / (prefix + 'inputs-before.json')).write_text(json.dumps(before,indent=2)+'\n')
commands = []
for name in ([] if probe_only else ['Fast','Inc']):
    commands.append(['lean','-DwarningAsError=true','--root='+str(packet/'src'),
                     '-o',str(cache/'ProbeView'/f'{name}.olean'),str(packet/'src/ProbeView'/f'{name}.lean')])
commands.append(['lean','-DwarningAsError=true',str(packet/'SiblingWait.lean')])
records = []
for index, command in enumerate(commands):
    t = time.monotonic()
    r = subprocess.run(command,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    out = packet / f'{prefix}command-{index}.out'
    out.write_text(r.stdout)
    record = {'command': command, 'exit_code': r.returncode, 'seconds': round(time.monotonic()-t,3),
              'output': out.name, 'sha256': sha(out)}
    records.append(record)
    print(json.dumps(record), flush=True)
    print(r.stdout, flush=True)
    if r.returncode:
        break
after = snapshot()
(packet/(prefix+'inputs-after.json')).write_text(json.dumps(after,indent=2)+'\n')
changed = [x for x in sorted(before.keys()|after.keys()) if before.get(x)!=after.get(x)]
result={'started':started,'reviewed_commit':revision,'review_base':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        'lean_version':subprocess.check_output(['lean','--version'],text=True).strip(),
        'lean_path':os.environ['LEAN_PATH'],'source_modules':len(sources),'inputs':len(before),
        'changed_inputs':changed,'commands':records,
        'all_commands_passed':len(records)==len(commands) and all(x['exit_code']==0 for x in records),
        'scope':'Finite probe; pinned research sources compiled here against recorded primary dependency artifacts; no universal theorem or runtime observation'}
(packet/(prefix+'result.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2),flush=True)
raise SystemExit(0 if result['all_commands_passed'] and not changed else 1)
