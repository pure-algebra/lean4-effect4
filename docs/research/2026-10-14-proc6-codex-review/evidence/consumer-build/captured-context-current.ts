import { readFileSync } from 'node:fs'
import { Effect, Exit, Layer, Scope } from '/Users/pooks/Dev/lean4-effect4/apps/todo/node_modules/effect/src/index.ts'
import * as Service from '/tmp/proc6-review-20261014/consumer-build/emitted-current/todo.gen.ts'
import { KeyedRecorder } from '/Users/pooks/Dev/lean4-effect4/harness/truth/session/keyed-recorder.ts'
import { provideRows, tableRows } from '/Users/pooks/Dev/lean4-effect4/harness/truth/session/keyed-bindings.ts'
const emitted=JSON.parse(readFileSync('/tmp/proc6-review-20261014/consumer-build/emitted-current/todo.table.json','utf8'))
const attempts:string[]=[]
const recorder=(name:string)=>new KeyedRecorder({name:'list',expression:'',table:emitted.table,source:null,plan:[],expected:null,live:true},name)
const a=recorder('a'),b=recorder('b')
const rowsFor=(label:string,r:KeyedRecorder)=>tableRows(emitted.application,emitted.table,(row,request,image)=>{attempts.push(label+':'+row.method);return r.external(row.index,image,Effect.succeed([]))})
const rowsA=rowsFor('A',a),rowsB=rowsFor('B',b)
const scope=Scope.makeUnsafe()
const context=await Effect.runPromise(provideRows(emitted.application,rowsA,emitted.services,Service,Layer.buildWithScope(Service.TodoAppLayer,scope)))
const method=Effect.gen(function*(){const todo=yield* Service.TodoApp;return yield* todo.list()})
const add=Effect.gen(function*(){const todo=yield* Service.TodoApp;return yield* todo.add('tea')})
const run=(r:KeyedRecorder,rows:any,program=method)=>Effect.runPromiseExit(Effect.withFiber(f=>{r.attachRoot(f);return provideRows(emitted.application,rows,emitted.services,Service,program.pipe(Effect.provide(context)))}))
const first=await run(a,rowsA)
const firstRecord=a.request([],first)
const second=await run(b,rowsB,add)
console.log(JSON.stringify({attempts,firstCalls:firstRecord.calls,firstSuccess:Exit.isSuccess(first),secondSuccess:Exit.isSuccess(second),secondCause:Exit.isFailure(second)?String(second.cause):null}))
await Effect.runPromise(Scope.close(scope,Exit.void))
