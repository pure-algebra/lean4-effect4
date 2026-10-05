import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { pathToFileURL } from 'node:url'
import assert from 'node:assert/strict'
const dir='/Users/pooks/.bun/install/cache/effect@3.22.2@@@1'
const {Effect,Fiber,STM,TRef}=await import(pathToFileURL(dir+'/dist/esm/index.js').href)
const hash=p=>createHash('sha256').update(readFileSync(p)).digest('hex')
const metadata={version:JSON.parse(readFileSync(dir+'/package.json','utf8')).version,runtime:{bun:process.versions.bun,nodeCompatibility:process.versions.node},compiler:'none; JavaScript entry and installed JavaScript dist',probeSha256:hash(new URL(import.meta.url)),sources:['src/STM.ts','src/internal/stm/stm.ts','src/internal/stm/core.ts','src/internal/stm/journal.ts'].map(p=>({path:dir+'/'+p,sha256:hash(dir+'/'+p)}))}
const settle=Effect.gen(function*(){for(let i=0;i<8;i++)yield* Effect.yieldNow()})
const writeRollback=(op,kind)=>Effect.gen(function*(){
 const ref=yield* STM.commit(TRef.make(0))
 const left=STM.gen(function*(){yield* TRef.set(ref,1);return yield* (kind==='retry'?STM.retry:STM.fail('left failed'))})
 const ex=yield* Effect.exit(STM.commit(STM[op](left,()=>TRef.get(ref))))
 return {op,kind,exit:ex._tag,result:ex._tag==='Success'?ex.value:null,after:yield* STM.commit(TRef.get(ref))}
})
const waitSet=op=>Effect.gen(function*(){
 const a=yield* STM.commit(TRef.make(0));const b=yield* STM.commit(TRef.make(0))
 let result='waiting'
 const body=ref=>STM.gen(function*(){const n=yield* TRef.get(ref);if(n===0)return yield* STM.retry;return n})
 const f=yield* Effect.fork(Effect.gen(function*(){result=yield* STM.commit(STM[op](body(a),()=>body(b)))}))
 yield* settle
 yield* STM.commit(TRef.set(a,1));yield* settle
 const afterA=result
 yield* STM.commit(TRef.set(b,2));yield* settle
 const afterB=result
 yield* Fiber.interrupt(f)
 return {op,afterA,afterB}
})
const deadline=setTimeout(()=>{console.error('probe deadline exceeded');process.exit(9)},10000)
try {
 const result=await Effect.runPromise(Effect.gen(function*(){return {writeRollback:[yield* writeRollback('orElse','retry'),yield* writeRollback('orTry','retry'),yield* writeRollback('orElse','fail'),yield* writeRollback('orTry','fail')],waitSet:[yield* waitSet('orElse'),yield* waitSet('orTry')]}}))
 assert.deepEqual(result.writeRollback.map(x=>[x.exit,x.result,x.after]),[['Success',0,0],['Success',1,1],['Success',0,0],['Failure',null,0]])
 assert.deepEqual(result.waitSet.map(x=>[x.afterA,x.afterB]),[['waiting',1],[1,1]])
 console.log(JSON.stringify({metadata,result,assertions:'passed'}))
}finally{clearTimeout(deadline)}
