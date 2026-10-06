from pathlib import Path
import subprocess,json,hashlib,re
root=Path('/Users/pooks/Dev/lean4-effect4')
out=Path('/private/tmp/codex-effect4-overnight-monitor/2026-10-06-decision-probes/literals')
rev='368e0314031cdc2376c38d5738bcb3cde4d099e0'
saved=Path('/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/e4a67264-1213-4b33-b3e2-68332653bd83/scratchpad/t5')
sources=[]
def src(path):
 b=subprocess.check_output(['git','show',rev+':'+path],cwd=root)
 sources.append({'path':path,'commit':rev,'sha256':hashlib.sha256(b).hexdigest()})
 return b.decode()
files={p:src('harness/truth/'+p) for p in ['prelude-atoms.gen.ts','prelude.ts','records.ts','tuples.ts','tuples.typecheck.ts','records.typecheck.ts','term-rows.typecheck.ts','folds.typecheck.ts','session/keyed-protocol.ts']}
for p in ['src/Effect4/Machine/Term.lean','src/Effect4/Program/NativeAtom.lean','docs/STATE.md','docs/core/decisions.md','tools/Effect4Gen/PreludeAtoms.lean']:
 src(p)
config=json.loads(src('harness/truth/tsconfig.json'))
config.pop('//',None);config.pop('include',None);config['files']=['term-rows.typecheck.ts','tuples.typecheck.ts','records.typecheck.ts','folds.typecheck.ts']
for variant in ['baseline','candidate','direct-assertion']:
 d=out/'inputs'/variant;d.mkdir(parents=True,exist_ok=True)
 for n,t in files.items():
  q=d/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(t)
 (d/'node_modules').symlink_to(root/'harness/truth/node_modules',target_is_directory=True)
 # expose the three known differences as ordinary compiler diagnostics
 p=d/'term-rows.typecheck.ts';t=p.read_text();a=t.index('// ---- a registered difference:');b=t.index('// ---- a list of number literals',a)
 t=t[:a]+re.sub(r'^\s*// @ts-expect-error.*\n','\n',t[a:b],flags=re.M)+t[b:];p.write_text(t)
 if variant!='baseline':
  p=d/'prelude-atoms.gen.ts';t=p.read_text()
  t=t.replace('export const pair = <const A, const B>(a: A, b: B): readonly [A, B] => [a, b]', 'type Wide<T> = T extends number ? number : T extends boolean ? boolean : T\nexport const pair = <const A, const B>(a: A, b: B): readonly [Wide<A>, Wide<B>] => [a, b] as unknown as readonly [Wide<A>, Wide<B>]')
  t=t.replace('export const tuple = <const A extends readonly unknown[]>(...items: A): A => items','export const tuple = <const A extends readonly unknown[]>(...items: A): { readonly [I in keyof A]: Wide<A[I]> } => items as unknown as { readonly [I in keyof A]: Wide<A[I]> }')
  if variant=='direct-assertion':t=t.replace(' as unknown as ',' as ')
  p.write_text(t)
 (d/'tsconfig.json').write_text(json.dumps(config,indent=2)+'\n')
for n in ['literal-widening-repair.md','skTryTake.txt','takeStep.txt','text-request.txt','skOffer.txt','skRetryTake.txt','skWithdraw.txt','offerStep.txt','withdrawTake.txt','withdrawOffer.txt']:
 p=saved/n
 if p.exists():
  q=out/'inputs'/'saved'/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());sources.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'kind':'retained seat input, no current generator run'})
(out/'source-hashes.json').write_text(json.dumps(sources,indent=2)+'\n')
print('Prepared three isolated variants and frozen source receipts')
