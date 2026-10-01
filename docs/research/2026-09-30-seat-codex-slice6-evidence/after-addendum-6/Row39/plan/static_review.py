from pathlib import Path
import json,re,hashlib,subprocess
root=Path('/Users/pooks/Dev/lean4-effect4-slice6');out=Path('/private/tmp/row39-series');meta=json.loads((out/'series.json').read_text())
original={}
for folder in ['src','Test','tools','harness']:
    for p in (root/folder).rglob('*.lean'):
        if any(x in p.parts for x in ['node_modules','.lake']):continue
        original[str(p.relative_to(root))]=p.read_text()
state=dict(original)
def imports(s):return re.findall(r'^import ([A-Za-z0-9_.]+)',s,re.M)
def module(p):
    if p.startswith('src/'):p=p[4:]
    elif p.startswith('tools/'):p=p[6:]
    return p[:-5].replace('/','.')
def comments(s):
    # Lean nested block comments and line comments; retain text in strings for inventory only.
    depth=0;result=[];i=0
    while i<len(s):
        if s.startswith('/-',i):depth+=1;i+=2;continue
        if depth and s.startswith('-/',i):depth-=1;i+=2;continue
        if depth:i+=1;continue
        if s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j;continue
        result.append(s[i]);i+=1
    return ''.join(result)
reports=[]
removed_modules=[]
for stage in meta['stages']:
    stage_root=out/stage['stage']/'rendered'
    for row in stage['changes']:
        p=row['path']
        if not p.endswith('.lean'):continue
        if row['action']=='delete':state.pop(p,None);removed_modules.append(module(p))
        else:state[p]=(stage_root/p).read_text()
    graph={module(p):imports(s) for p,s in state.items() if p.startswith(('src/','Test/','tools/'))}
    bad_imports=[(m,x) for m,imps in graph.items() for x in imps if x in removed_modules]
    cycles=[];done=set()
    def visit(m,active):
        if m in active:cycles.append(active+[m]);return
        if m in done:return
        done.add(m)
        for x in graph.get(m,[]):visit(x,active+[m])
    for start in graph:visit(start,[])
    def reach(start):
        seen=set();stack=[start]
        while stack:
            m=stack.pop()
            if m in seen:continue
            seen.add(m);stack.extend(graph.get(m,[]))
        return seen
    lib=reach('Effect4')|reach('Effect4.Laws');tests=reach('Test.All')
    new_or_modified=[row['path'] for row in stage['changes'] if row['path'].endswith('.lean') and row['action']!='delete']
    unreachable=[p for p in new_or_modified if (p.startswith('src/Effect4') and module(p) not in lib) or (p.startswith('Test/') and module(p) not in tests)]
    # Direct retired identifiers, not the retained Schema.Check constructor namespace.
    patterns=[r'\bEffectfulField(?:Spec)?\b',r'\bFieldEffectOps\b']
    if stage['stage']>='02':patterns += [r'\bfieldAdmissible\b',r'\bFieldAdmissible\b',r'\bProgramImage\b',r'Schema\.Predicate\.',r'Schema\.check\b',r'Codegen\.Schema\.(?:generate\?|source\?|module\?|documentReady|generationReady|GenerationReady)']
    if stage['stage']>='03':patterns += [r'\bannotationBags\b',r'\bAnnotationTraversal\b',r'Annotations\.payloadsAt']
    hits=[]
    for p,s in state.items():
        stripped=comments(s)
        for pat in patterns:
            if re.search(pat,stripped):hits.append((p,pat))
    report={'stage':stage['stage'],'imports_of_deleted_modules':bad_imports,'cycles':cycles,'modified_unreachable_modules':unreachable,'retired_active_identifier_hits':hits}
    if stage['stage']=='04-of-shape':report['schema_modules_in_pure_shape_closure']=sorted(x for x in reach('Effect4.Store.Domain.Shape') if x.startswith('Effect4.Schema'))
    reports.append(report)
# Exact operational renderer block (proofs excluded) + guard text equality.
before=(root/'src/Effect4/Store/Domain/Shape.lean').read_text();after=state['src/Effect4/Schema/OfShape.lean']
segments=[('def identifierKey :','theorem identifierKey_lawful'),('def refKey :','theorem refKey_lawful'),('/-! ## The spec: `ShapeDoc.document` -/','/-! ## The printer: `ShapeDoc.print` -/')]
checks=[]
for start,end in segments:
    a=before[before.index(start):before.index(end,before.index(start))]
    if end.startswith('/-! ## The printer'):b=after[after.index(start):after.index('/-! Existing finite rendering receipts')]
    else:b=after[after.index(start):after.index(end,after.index(start))]
    checks.append({'segment':start,'identical':a==b})
for report in reports:
    assert not any(report[k] for k in ['imports_of_deleted_modules','cycles','modified_unreachable_modules','retired_active_identifier_hits']),report
assert all(x['identical'] for x in checks),checks
assert not reports[-1]['schema_modules_in_pure_shape_closure']
(out/'static-closure-review.json').write_text(json.dumps({'stages':reports,'renderer_definition_text':checks,'claims':'Static source inventory/import/body comparison only; no Lean elaboration or semantic proof'},indent=2)+'\n')
print(json.dumps({'stages':len(reports),'all_static_checks_passed':True,'renderer_definition_segments_identical':len(checks)}))
