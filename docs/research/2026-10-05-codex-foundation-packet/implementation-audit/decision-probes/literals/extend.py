from pathlib import Path
import shutil,json,re
out=Path(__file__).parent
for n,origin in [('revised','direct-assertion'),('contextual','baseline'),('blanket-mutant','direct-assertion')]:
 shutil.copytree(out/'inputs'/origin,out/'inputs'/n,symlinks=True)
pre='''import { type Deferred, Effect, type Option, Ref } from "effect"
import { add,append,cons,fold,get,isZero,ite,length,lt,mul,nil,none,not,pair,recordRequired,recordSet,recordValue,sameHandle,some,succ,take,tuple,tupleAt,and,isSome,or,sub,drop,eq } from "./prelude.ts"
type Hint = Deferred.Deferred<void, never>
type Taker = { readonly hint: Hint; readonly id: Hint }
type Offer = { readonly batch: boolean; readonly hint: Deferred.Deferred<boolean,never>; readonly id: Hint; readonly rest: ReadonlyArray<number> }
type Steps = { readonly msgs: ReadonlyArray<number>; readonly takers: ReadonlyArray<Taker>; readonly offers: ReadonlyArray<Offer>; readonly cap: number }
'''
expr=(out/'inputs/saved/takeStep.txt').read_text().strip()
for n in ['baseline','candidate','direct-assertion','revised','contextual','blanket-mutant']:
 d=out/'inputs'/n
 q=pre+'export const takeStep = (a0: Ref.Ref<Steps>, a1: Hint, a2: Hint): Effect.Effect<readonly [Option.Option<number>, ReadonlyArray<Offer>, ReadonlyArray<Taker>]> =>\n'+expr+'\n'
 if n=='contextual':
  q=q.replace('(a3) =>','(a3): readonly [readonly [Option.Option<number>, ReadonlyArray<Offer>, ReadonlyArray<Taker>], Steps] =>',1)
  p=d/'term-rows.typecheck.ts';t=p.read_text();a=t.index('const request =');b=t.index('// ---- a list of number literals',a);part=t[a:b]
  part=part.replace('(a1) => ite(', '(a1): readonly [boolean, Window] => ite(',1)
  part=part.replace('(a2) => ite(', '(a2): readonly [readonly [Option.Option<number>,number,Option.Option<Hint>],Skeleton] => ite(',1)
  part=part.replace('tuple(0, false), (a0, a1) =>', 'tuple<number, boolean>(0, false), (a0, a1) =>') if False else part
  # The two caller annotations are deliberately the only contextual alternative.
  p.write_text(t[:a]+part+t[b:])
 (d/'real-queue-take.ts').write_text(q)
 c=json.loads((d/'tsconfig.json').read_text());c['files'].append('real-queue-take.ts');(d/'tsconfig.json').write_text(json.dumps(c,indent=2)+'\n')
for n in ['revised','blanket-mutant']:
 d=out/'inputs'/n;p=d/'tuples.typecheck.ts';t=p.read_text()
 for a,b in [('const singleton: readonly [7]', 'const singleton: readonly [number]'),('const pair: readonly [7, "x"]','const pair: readonly [number, "x"]'),('const larger: readonly [7, "x", true]','const larger: readonly [number, "x", boolean]'),('const first: 7 =','const first: number ='),('const third: true =','const third: boolean ='),('const nested: 7 =','const nested: number =')]:t=t.replace(a,b)
 p.write_text(t)
p=out/'inputs/blanket-mutant/prelude-atoms.gen.ts';t=p.read_text();t=t.replace('type Wide<T> = T extends number ? number : T extends boolean ? boolean : T','type Wide<T> = T extends number ? number : T extends boolean ? boolean : T extends string ? string : T');p.write_text(t)
print('Added exact retained Queue take, context-only alternative, revised pins and string-widening mutant')
