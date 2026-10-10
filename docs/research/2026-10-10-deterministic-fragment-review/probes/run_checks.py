"""Run only the retained design probes, sequentially under lake env."""
import json, os, pathlib, subprocess, time, sys
root = pathlib.Path(__file__).resolve().parent
os.environ['LEAN_NUM_THREADS'] = '3'
os.environ['LEAN_PATH'] = str(root) + ':' + os.environ.get('LEAN_PATH', '')
files = sys.argv[1:] or ['ReviewRandomDescent', 'Audit', 'ReviewTapes', 'Fragment', 'Controls']
results = []
for name in files:
    command = ['lean', '-o', str(root / (name + '.olean')), str(root / (name + '.lean'))]
    started = time.monotonic()
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (root / (name + '.out')).write_text(result.stdout)
    row = {'file': name + '.lean', 'command': command, 'exit': result.returncode,
           'seconds': round(time.monotonic() - started, 3)}
    results.append(row)
    print(json.dumps(row), flush=True)
    if result.returncode:
        print(result.stdout, flush=True)
        break
(root / ('results-' + '-'.join(files) + '.json')).write_text(json.dumps(results, indent=2) + '\n')
sys.exit(results[-1]['exit'])
