import { Context, Effect, Exit, Layer, Ref, Scope } from '/Users/pooks/Dev/lean4-effect4/apps/todo/node_modules/effect/src/index.ts'
let built=0
const Cell=Context.Service<any,any>('ProbeCell')
const layer=Layer.effect(Cell,Effect.gen(function*(){built++;return yield* Ref.make(0)}))
const increment=Effect.gen(function*(){const ref=yield* Cell;return yield* Ref.updateAndGet(ref,(n:number)=>n+1)})
const perRequest=[]
for(let i=0;i<2;i++)perRequest.push(await Effect.runPromise(increment.pipe(Effect.provide(layer))))
const scope=Scope.makeUnsafe()
const context=await Effect.runPromise(Layer.buildWithScope(layer,scope))
const startup=[]
for(let i=0;i<2;i++)startup.push(await Effect.runPromise(increment.pipe(Effect.provide(context))))
await Effect.runPromise(Scope.close(scope,Exit.void))
console.log(JSON.stringify({perRequest,startup,built}))
