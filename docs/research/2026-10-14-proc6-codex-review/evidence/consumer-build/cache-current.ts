import { Effect, Exit, Layer, Option, Scope } from '/Users/pooks/Dev/lean4-effect4/apps/todo/node_modules/effect/src/index.ts'
import * as Service from './emitted-current/todo.gen.ts'
let todos:any[]=[];const calls:string[]=[]
const repo={all:()=>Effect.sync(()=>{calls.push('all');return [...todos]}),insert:(title:string)=>Effect.sync(()=>{calls.push('insert');const todo={id:todos.length+1,title,done:false};todos.push(todo);return todo}),setDone:()=>Effect.succeed(Option.none()),delete:()=>Effect.succeed(false)}
const scope=Scope.makeUnsafe()
const context=await Effect.runPromise(Layer.buildWithScope(Service.TodoAppLayer,scope).pipe(Effect.provideService(Service.TodoRepo,repo)))
const run=(use:any)=>Effect.runPromise(Effect.gen(function*(){const todo=yield* Service.TodoApp;return yield* use(todo)}).pipe(Effect.provide(context)))
const first=await run((todo:any)=>todo.list());const afterFirst=[...calls]
const hit=await run((todo:any)=>todo.list());const afterHit=[...calls]
const added=await run((todo:any)=>todo.add('tea'));const afterAdd=[...calls]
const afterWrite=await run((todo:any)=>todo.list());const afterWriteCalls=[...calls]
console.log(JSON.stringify({first,hit,added,afterWrite,afterFirst,afterHit,afterAdd,afterWriteCalls}))
await Effect.runPromise(Scope.close(scope,Exit.void))
