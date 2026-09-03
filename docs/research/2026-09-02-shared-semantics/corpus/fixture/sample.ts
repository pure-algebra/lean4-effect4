import { Effect as E, Layer as L } from 'effect';
import * as FX from 'effect';
import * as SE from 'effect/Effect';
import { gen as makeGen } from 'effect/Effect';
import type { Effect as TypeOnly } from 'effect';
const alias=E;
const {race:compete}=E;
const scoped=L.scoped;
alias.gen(function*(){
  for(let i=0;i<3;i++){yield* E.succeed(i)}
  function helper(){while(false){}}
  yield* E.gen(function*(){while(false){yield* E.succeed(0)}});
});
E['catchAll'](null as any);
FX.Effect.fork(null as any);
SE.race(null as any);
makeGen(function*(){ return 1 });
compete(null as any);
scoped(null as any,null as any);
function shadow(E:any){ E.gen(function*(){while(true){}}) }
function shadowAlias(alias:any){ alias.gen(function*(){while(true){}}) }
class Base extends (class { static x=E.gen(function*(){ return 2 }) }) {}
L.empty.pipe((x)=>x);
type T=typeof makeGen;
