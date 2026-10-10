"""Run the slice's checks serially and retain measured commands and results."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REPORT = HERE / 'verification.json'
ENV = {**os.environ, 'LEAN_NUM_THREADS': '3'}
SOURCES = ['tools/Tools/Graph/Index.lean', 'tools/Tools/View/Flow.lean',
           'tools/Tools/View/FlowLaws.lean']
JOBS = [
    ('narrow-build', ['lake', 'build', 'Tools.Graph.Index', 'Tools.View.Flow',
        'Tools.View.FlowLaws', 'Tools.View.FlowPath', 'Tools.View.FlowOrder',
        'Tools.View.FlowSpecimen', 'Tools.View.Build', 'ProofGraph.AxiomAudit']),
    ('audit', ['lake', 'env', 'lean', '-DwarningAsError=true', str(HERE / 'Audit.lean')]),
    ('controls', ['lake', 'env', 'lean', '-DwarningAsError=true', str(HERE / 'Controls.lean')]),
    ('benchmark', ['lake', 'env', 'lean', '-DwarningAsError=true', '--run', str(HERE / 'Benchmark.lean')]),
    ('inspection', ['python3', str(HERE / 'inspect.py')]),
    ('summary', ['python3', str(HERE / 'summarize.py')]),
    ('language', ['python3', 'scripts/check-language.py', '--strict',
        str(HERE / 'PLAN.md'), str(HERE / 'README.md')]),
]
selected = set(sys.argv[1:])
record = json.loads(REPORT.read_text()) if REPORT.exists() else {'checks': {}}
record.update({'base': subprocess.check_output(['git', 'rev-parse', '9389e543'], cwd=ROOT, text=True).strip(),
    'source_head': subprocess.check_output(['git', 'log', '-1', '--format=%H', '--', *SOURCES], cwd=ROOT, text=True).strip(), 'lean_num_threads': 3,
    'scope': 'Exact local proofs and finite controls; Lean assignment timings, no renderer timing.'})
for name, command in JOBS:
    if selected and name not in selected:
        continue
    hashes = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES}
    started = time.monotonic()
    log = HERE / (name + '.log')
    with log.open('w') as out:
        result = subprocess.run(command, cwd=ROOT, env=ENV, stdout=out, stderr=subprocess.STDOUT)
    item = {'command': command, 'exit_code': result.returncode,
            'elapsed_seconds': round(time.monotonic() - started, 3),
            'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'production_sha256': hashes, 'log': str(log.relative_to(ROOT)),
            'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest()}
    record['checks'][name] = item
    record['all_passed'] = all(j[0] in record['checks'] and record['checks'][j[0]]['exit_code'] == 0
                               for j in JOBS)
    REPORT.write_text(json.dumps(record, indent=2) + '\n')
    print(name, result.returncode, item['elapsed_seconds'], flush=True)
    if result.returncode:
        print(log.read_text()[-10000:])
        raise SystemExit(result.returncode)
