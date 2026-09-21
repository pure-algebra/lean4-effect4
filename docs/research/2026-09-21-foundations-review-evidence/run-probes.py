#!/usr/bin/env python3
"""Run the focused review probes sequentially. No generated or production files change."""
import argparse
import hashlib
import json
import re
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
parser = argparse.ArgumentParser()
parser.add_argument('--skip-build', action='store_true', help='Use the already completed narrow build')
args = parser.parse_args()
commands = []
if not args.skip_build:
    commands.append(('build', ['lake', 'build', 'Effect4.Laws.Program.Typed.Contracts',
                              'Effect4.Laws.Machine.Refinement', 'Effect4.Laws.Program.EvaluateR']))
for name, file in [('answer-shape', 'AnswerShapeProbe.lean'),
                   ('monotonicity-bridge', 'MonotonicityBridgeProbe.lean'),
                   ('protocol-admission', 'ProtocolAdmissionProbe.lean'),
                   ('world-replay', 'WorldReplayProbe.lean'),
                   ('stack', 'StackProbe.lean'),
                   ('architecture-statements', 'ArchitectureStatements.lean')]:
    commands.append((name, ['lake', 'env', 'lean', '-DwarningAsError=true', str(HERE / file)]))
results = []
for name, command in commands:
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (HERE / f'{name}.log').write_text(result.stdout)
    axiom_sets = re.findall(r"depends on axioms: \[([^\]]*)\]", result.stdout, re.S)
    unexpected = sorted({a.strip() for group in axiom_sets for a in group.split(',')
                         if a.strip() and a.strip() not in {'propext', 'Quot.sound'}})
    item = {'name': name, 'command': command, 'exit_code': result.returncode,
            'unexpected_axioms': unexpected}
    if name != 'build':
        source = Path(command[-1]).read_text()
        declared = re.findall(r'^theorem ([A-Za-z0-9_]+)', source, re.M)
        printed = re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", result.stdout)
        item['declaration_kind'] = 'open_obligation_wrappers' if name == 'architecture-statements' else 'research_theorems'
        item['declared_theorems'] = len(declared)
        if name == 'architecture-statements':
            item['ledger_ok'] = '4 open, 0 proved, 4 total; ceiling 4' in result.stdout
        item['missing_axiom_reports'] = [n for n in declared
                                         if not any(full.endswith('.' + n) for full in printed)]
    results.append(item)
    print(f'{name}: exit {result.returncode}', flush=True)
manifest = {'base': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
            'results': results,
            'sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(HERE.glob('*.lean'))}}
(HERE / 'results.json').write_text(json.dumps(manifest, indent=2) + '\n')
raise SystemExit(int(any(r['exit_code'] != 0 or r['unexpected_axioms'] or r.get('missing_axiom_reports') or not r.get('ledger_ok', True) for r in results)))
