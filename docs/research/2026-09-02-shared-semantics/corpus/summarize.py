import json,collections,re,hashlib
from pathlib import Path
p=Path('/tmp/effect-q9-research')
x=json.loads((p/'scan.json').read_text()); inv=json.loads((p/'inventory.json').read_text())
def sites(rows):
 return {'sites':len(rows),'files':len(set((r['repo'],r['file']) for r in rows)),'repos':len(set(r['repo'] for r in rows))}
def testpath(f):return bool(re.search(r'(^|/)(test|tests|__tests__|__snapshots__|fixtures|examples|perf|benchmark|benchmarks)(/|$)|\.(test|spec)\.[cm]?tsx?$',f))
out={'typescript':x['typescript'],'sourceDigest':x['sourceDigest'],'repoPinDigest':x['repoPinDigest'],'files':len(x['files']),'parseErrorFiles':len(x['errors']),'importedFiles':len(set((r['repo'],r['file']) for r in x['imports'])),'groups':{},'operations':{},'perRepo':[],'generator':{},'strata':{},'lexical':{}}
for group in ['Layer','Scope-module','resource','fork','race','catch','gen']:
 out['groups'][group]={'references':sites([r for r in x['refs'] if r['group']==group]),'calls':sites([r for r in x['calls'] if r['group']==group])}
for op in sorted(set(r['op'] for r in x['refs'])):
 out['operations'][op]={'references':sites([r for r in x['refs'] if r['op']==op]),'calls':sites([r for r in x['calls'] if r['op']==op])}
def genstats(gs):
 gi=[g for g in gs if g['inline']]
 out={'calls':len(gs),'inlineBodies':len(gi),'withNestedGen':sum(g['lexicalNested']>0 for g in gi),'depths':dict(collections.Counter(g['nestingDepth'] for g in gs)),'directLoopBodies':sum(g['direct']['loops']>0 for g in gi),'lexicalLoopBodies':sum(g['lexical']['loops']>0 for g in gi),'directLoops':sum(g['direct']['loops'] for g in gi),'directLoopKinds':dict(sum((collections.Counter(g['direct']['loopKinds']) for g in gi),collections.Counter())),'directBodyWith':{k:sum(g['direct'][k]>0 for g in gi) for k in ['ifs','switches','tries','finally','breaks','continues','labeledBreaks','labeledContinues','yields','throws','returns','functions','loopYield']}}
 out['noDirectIfSwitchLoopTry']=sum(not any(g['direct'][k] for k in ['ifs','switches','loops','tries']) for g in gi)
 return out
out['generator']=genstats(x['gens'])
for r in inv['repos']:
 if not r['listed']:continue
 rr=[v for v in x['refs'] if v['repo']==r['repo']]; cc=[v for v in x['calls'] if v['repo']==r['repo']]
 out['perRepo'].append({'repo':r['repo'],'pin':r['head'],'files':len(r['analysis_files']),'referencesByGroup':dict(collections.Counter(v['group'] for v in rr)),'callsByGroup':dict(collections.Counter(v['group'] for v in cc)),'generator':genstats([v for v in x['gens'] if v['repo']==r['repo']])})
for stratum,pred in [('test-fixture-example-benchmark-path',lambda r:testpath(r['file'])),('other-path',lambda r:not testpath(r['file'])),('excluding-alchemy',lambda r:r['repo']!='alchemy-run_alchemy')]:
 out['strata'][stratum]={'files':sum(pred(r) for r in x['files']),'referencesByGroup':dict(collections.Counter(r['group'] for r in x['refs'] if pred(r))),'callsByGroup':dict(collections.Counter(r['group'] for r in x['calls'] if pred(r))),'generator':genstats([g for g in x['gens'] if pred(g)])}
for f in x['files']:
 for k,n in f['lexical'].items():out['lexical'][k]=out['lexical'].get(k,0)+n
(p/'summary.json').write_text(json.dumps(out,indent=2)+'\n')
(p/'selected-pins.tsv').write_text(''.join(r['repo']+'\t'+r['head']+'\n' for r in inv['repos'] if r['listed']))
(p/'per-repo.tsv').write_text('repo\tfiles\tLayer-refs\tresource-refs\tScope-refs\tfork-refs\trace-refs\tcatch-refs\tgen-calls\tdirect-loop-bodies\tnested-gen-bodies\n'+''.join('\t'.join(map(str,[r['repo'],r['files'],*[r['referencesByGroup'].get(k,0) for k in ['Layer','resource','Scope-module','fork','race','catch']],r['generator']['calls'],r['generator']['directLoopBodies'],r['generator']['withNestedGen']]))+'\n' for r in out['perRepo']))
print(json.dumps({k:v for k,v in out.items() if k not in ['operations','perRepo','lexical']},indent=2))
for group in ['Layer','resource','fork','race','catch']:
 print(group,sorted(((k,v['references']['sites'],v['calls']['sites']) for k,v in out['operations'].items() if k.startswith(group+'.') or any(r['op']==k and r['group']==group for r in x['refs'])),key=lambda t:-t[1]))
print('lexical-gen',out['lexical'].get('Effect.gen'),'lexical-fn',out['lexical'].get('Effect.fn'))
