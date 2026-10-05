from pathlib import Path
from collections import deque
import hashlib, json, platform, subprocess

ROOT = Path('/Users/pooks/Dev/lean4-effect4')
OUT = Path('/private/tmp/codex-effect4-overnight-monitor/2026-10-05-proof-scouting-followup')

def unique(xs):
    return list(dict.fromkeys(xs))

def revised(edges, bound, start):
    reached, todo = [], unique(start)
    for _ in range(bound):
        if not todo:
            break
        n, todo = todo[0], todo[1:]
        reached.append(n)
        todo += [d for d in unique(edges.get(n, [])) if d not in reached and d not in todo]
        assert len(reached) == len(set(reached))
        assert len(todo) == len(set(todo))
        assert not set(reached) & set(todo)
    return reached, todo

def oracle(edges, start):
    seen, todo, result = set(), deque(start), []
    while todo:
        n = todo.popleft()
        if n in seen:
            continue
        seen.add(n)
        result.append(n)
        todo.extend(edges.get(n, []))
    return result

def old(edges, start):
    reached, todo = [], list(start)
    for _ in range(len(edges) + 1):
        if not todo:
            break
        n = todo.pop(0)
        if n in reached:
            continue
        reached.append(n)
        todo.extend(edges.get(n, []))
    return reached, todo

shared = {'T':['A','B','C'], 'A':['D'], 'B':['D'], 'C':['D'], 'D':['L'], 'L':[]}
chain = {'T':['A'], 'A':['B'], 'B':['C'], 'C':['D'], 'D':['L'], 'L':[]}
whole = ['T','A','B','C','D','L']
cases = [
    ('shared descendant', shared, 6, ['T'], (whole, [])),
    ('chain positive control', chain, 6, ['T'], (whole, [])),
    ('repeated starting node', shared, 6, ['T','T'], (whole, [])),
    ('small budget retains pending', shared, 3, ['T'], (['T','A','B'], ['C','D'])),
    ('zero budget retains distinct starts', shared, 0, ['T','T','A'], ([], ['T','A'])),
    ('cycle and self-loop', {'T':['T','A'], 'A':['T','B'], 'B':['A','B']}, 3, ['T'], (['T','A','B'], [])),
    ('duplicate sibling edges', {'T':['A','A','B','A'], 'A':['B','L','L'], 'B':['L'], 'L':[]}, 4, ['T'], (['T','A','B','L'], [])),
    ('missing start and edge names in renderer bound', {'T':['outside']}, 4, ['absent','T'], (['absent','T','outside'], [])),
]
rows=[]
for label,edges,bound,start,want in cases:
    got=revised(edges,bound,start)
    assert got == want, (label, got, want)
    if not got[1]:
        assert got[0] == oracle(edges,start)
    rows.append({'label':label,'edges':edges,'bound':bound,'start':start,'reached':got[0],'pending':got[1]})
assert old(shared,['T'])[0] == ['T','A','B','C','D']
assert old(chain,['T'])[0] == whole
reportpath=ROOT/'.lake/gen/semantics-report/semantics.json'
report=json.loads(reportpath.read_text())
edges={n['name']:n['broughtIn']['nearest'] for n in report['plan']['nodes']}
names=unique([x for n,ds in edges.items() for x in [n]+ds])
retained=[]
for r in report['plan']['requirements']:
    starts=[n['name'] for n in r['top']+r['placed']]
    got,pending=revised(edges,len(names)+len(starts),starts)
    assert got == oracle(edges,starts)
    assert pending == []
    retained.append({'requirement':r['id'],'visited':len(got),'pending':len(pending)})
paths=['tools/Tools/Semantics.lean','tools/Drivers/SemanticsControls.lean','.lake/gen/semantics-report/semantics.json']
data={'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'python':platform.python_version(),'scope':'Finite Python mirror and independent traversal oracle; no Lean execution. Eight synthetic cases, old red/green control, retained report comparison.','source_sha256':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths},'old_shared':old(shared,['T']),'old_chain':old(chain,['T']),'cases':rows,'retained_report':retained}
(OUT/'reach-followup.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'head':data['head'],'python':data['python'],'synthetic_cases_passed':len(rows),'old_red_and_green_passed':True,'retained_requirement_comparisons_passed':len(retained),'scope':data['scope']}))
