from pathlib import Path
import hashlib, json, os, subprocess, sys, time
from datetime import datetime, timezone
p = Path(__file__).resolve().parent
owner = Path('/Users/pooks/Dev/lean4-effect4-wt/module-layers')
lib = p / '.repair-lib'
lib.mkdir(exist_ok=True)
env = os.environ.copy()
env['LEAN_NUM_THREADS'] = '3'
env['LEAN_PATH'] = str(lib) + ':' + str(owner / '.lake/build/lib/lean') + ':' + env.get('LEAN_PATH', '')
files = [p / 'Repair.lean', p / 'SplitControl.lean',
         owner / 'src/Effect4/Laws/Codegen/ReadPrint.lean',
         owner / '.lake/build/lib/lean/Effect4/Laws/Codegen/ReadPrint.olean']
def hashes():
    return {str(f): hashlib.sha256(f.read_bytes()).hexdigest() for f in files}
before = hashes()
results = []
passed = True
for module, expected_audit in [('SplitControl', 1), ('Repair', 0)]:
    commands = [('compile', ['lean', '-M4096', '-DwarningAsError=true', '-R', str(p),
                '-o', str(lib / (module + '.olean')), str(p / (module + '.lean'))], 0),
                ('audit', ['lean', '-M4096', '-DwarningAsError=true',
                str(p / (module + 'Audit.lean'))], expected_audit)]
    for action, cmd, expected in commands:
        start = time.monotonic()
        r = subprocess.run(cmd, env=env, text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, timeout=180)
        ok = r.returncode == expected
        if action == 'audit' and expected == 1:
            ok = ok and '2 of 58 declarations' in r.stdout and 'Pi.instNonempty' in r.stdout
        item = {'name': module + '-' + action, 'argv': cmd, 'exit': r.returncode,
                'expected_exit': expected, 'passed': ok,
                'seconds': round(time.monotonic() - start, 3), 'output': r.stdout}
        results.append(item)
        (p / (module + '-' + action + '.log')).write_text(r.stdout)
        print(json.dumps(item), flush=True)
        if not ok:
            passed = False
            break
    if not passed:
        break
after = hashes()
passed = passed and before == after
out = {'checked_at': datetime.now(timezone.utc).isoformat(), 'passed': passed,
       'commands': results, 'before': before, 'after': after, 'lean_path': env['LEAN_PATH']}
(p / 'repair-controls.json').write_text(json.dumps(out, indent=2) + '\n')
sys.exit(0 if passed else 1)
