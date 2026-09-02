#!/usr/bin/env python3
"""Check supervision evidence shape against its frozen authored packet.

The generator supplies fresh Lean output and separately pins the packet bytes.
This checker is also used for negative candidate tests; acceptance alone is
not a proof, a host run, or permission to close an external graph obligation.
"""

from pathlib import Path
from collections import Counter
import re
import sys

if len(sys.argv) != 5:
    raise SystemExit("usage: check-supervision-evidence.py evidence.tsv battery.lean axioms.lean DAG.md")
rows = [line.split('\t') for line in Path(sys.argv[1]).read_text().splitlines()]
counts = Counter(row[0] for row in rows)
expected = {'owned-declaration': 705, 'api': 294, 'theorem': 136, 'axiom': 136,
            'type': 27, 'shape': 19, 'leaf-receipt': 3, 'graph-edge': 10}
if dict(counts) != expected:
    raise SystemExit(f'FAIL Supervision evidence counts: {dict(counts)}')
for kind in counts:
    values = [row[1] for row in rows if row[0] == kind]
    if len(set(values)) != len(values):
        raise SystemExit(f'FAIL duplicate Supervision {kind} receipt')
api = [row[1] for row in rows if row[0] == 'api']
battery = re.findall(r'#check \(@([^\s]+)\s*:', Path(sys.argv[2]).read_text())
if api != battery:
    raise SystemExit('FAIL Supervision authored API differs from the exact frozen battery')
theorems = [row[1] for row in rows if row[0] == 'theorem']
reports = re.findall(r'^#print axioms (\S+)', Path(sys.argv[3]).read_text(), re.M)
if theorems != reports:
    raise SystemExit('FAIL Supervision theorem receipts differ from the frozen axiom report')
for row in rows:
    if row[0] == 'axiom' and row[2] not in ('none', 'propext', 'Quot.sound', 'propext,Quot.sound'):
        raise SystemExit('FAIL Supervision axiom ceiling')
    if row[0] == 'graph-edge':
        edge = row[1].rsplit('/', 1)[1]
        expected_state = 'not-applicable' if edge == 'REPRESENTATION' else (
            'required-open' if edge in ('BRIDGES', 'TARGETS', 'TRUST') else 'required-local')
        if row[3] != expected_state:
            raise SystemExit(f'FAIL Supervision source boundary relabeled: {edge}')
dag_graph = Path(sys.argv[4]).read_text().split('## Graph-edge ledger', 1)[1].split(
    'A controller implementation', 1)[0]
expected_edges = ['SUPERVISION-PG-RC112/' + line.split('|')[1].strip().upper()
                  for line in dag_graph.splitlines()
                  if re.match(r'^\| [a-z]+ \|', line)]
if len(expected_edges) != 10 or [row[1] for row in rows if row[0] == 'graph-edge'] != expected_edges:
    raise SystemExit('FAIL Supervision graph edge identifiers differ from the frozen DAG')
# Every generated type disposition must retain its exact breaker allocation.
dag_text = Path(sys.argv[4]).read_text()
type_section = dag_text.split('## Complete type and judgment disposition', 1)[1].split(
    '`Fiber.toFiberState_eq`', 1)[0]
expected_types = []
for line in type_section.splitlines():
    if not line.startswith('| `'):
        continue
    name, disposition, relation, route = [cell.strip() for cell in line.strip('|').split('|')]
    name = name.strip('`')
    expected_types.append(['type', 'SUP-TYPE-' + name, 'Effect4.Supervision.' + name,
        'Effect4.Concurrency.Supervision', disposition, route.strip('`')])
if [row for row in rows if row[0] == 'type'] != expected_types:
    raise SystemExit('FAIL Supervision type receipts differ from frozen dispositions and routes')
expected_leaves = [['leaf-receipt', row[5], row[2], 'SUPERVISION-PG-RC112/CONSTRUCTION',
                    row[2] + '.cases_receipt'] for row in expected_types if row[5].startswith('SUP-L-')]
if [row for row in rows if row[0] == 'leaf-receipt'] != expected_leaves:
    raise SystemExit('FAIL Supervision finite-leaf routes differ from the frozen DAG')
# Shape rows are independently compared with the breaker's authored table.
text = Path(sys.argv[4]).read_text().split('## Exact shape expectations', 1)[1].split(
    'No local metadata checker', 1)[0]
expected_shapes = []
for line in text.splitlines():
    if not line.startswith('| `'):
        continue
    name, constructors, fields = [cell.strip() for cell in line.strip('|').split('|')]
    expected_shapes.append(['shape', 'Effect4.Supervision.' + name.strip('`'),
        ','.join('Effect4.Supervision.' + x for x in re.findall(r'`([^`]+)`', constructors)),
        'inductive' if fields == '—' else ','.join(re.findall(r'`([^`]+)`', fields))])
if [row for row in rows if row[0] == 'shape'] != expected_shapes:
    raise SystemExit('FAIL Supervision shape receipts differ from frozen constructors and fields')
