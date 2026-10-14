import { Effect, Option } from '/Users/pooks/Dev/lean4-effect4/apps/todo/node_modules/effect/src/index.ts'
import { cachedListAfterAdd } from './consumer-current.ts'
import * as Service from './emitted/todo.gen.ts'
let todos:any[]=[];const calls:string[]=[]
const repo={all:()=>Effect.sync(()=>{calls.push('all');return [...todos]}),insert:(title:string)=>Effect.sync(()=>{calls.push('insert');const todo={id:todos.length+1,title,done:false};todos.push(todo);return todo}),setDone:()=>Effect.succeed(Option.none()),delete:()=>Effect.succeed(false)}
const result=await Effect.runPromise(cachedListAfterAdd('tea').pipe(Effect.provideService(Service.TodoRepo,repo)))
console.log(JSON.stringify({result,calls}))
