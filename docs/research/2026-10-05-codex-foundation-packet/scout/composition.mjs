import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { pathToFileURL } from 'node:url'
const variant = process.argv[2]
const dirs = {
  rc112: '/Users/pooks/Dev/lean4-effect4/vendor/effect-4.0.0-rc.112',
  v401: '/Users/pooks/.bun/install/cache/effect@4.0.1@@@1'
}
const dir = dirs[variant]
if (!dir) throw new Error('choose rc112 or v401')
const Effect = await import(pathToFileURL(dir + '/src/Effect.ts').href)
const TxRef = await import(pathToFileURL(dir + '/src/TxRef.ts').href)
const hash = path => createHash('sha256').update(readFileSync(path)).digest('hex')
const metadata = {
 variant,
 packageVersion: variant === 'v401' ? JSON.parse(readFileSync(dir + '/package.json', 'utf8')).version : '4.0.0-rc.112 (vendored source path)',
 runtime: { bun: process.versions.bun, nodeCompatibility: process.versions.node },
 compiler: 'none; JavaScript entry, Bun TypeScript source loader',
 imports: ['src/Effect.ts','src/TxRef.ts','src/internal/effect.ts'].map(p => ({path:dir+'/'+p,sha256:hash(dir+'/'+p)})),
 probeSha256: hash(new URL(import.meta.url))
}
const deadline = setTimeout(() => { console.error('probe deadline exceeded'); process.exit(9) }, 10000)
const nested = caught => Effect.gen(function* () {
 const ref = yield* TxRef.make(0)
 let innerExit = 'not captured'
 const wholeExit = yield* Effect.exit(Effect.tx(Effect.gen(function* () {
  const inner = Effect.tx(Effect.gen(function* () { yield* TxRef.set(ref, 1); yield* Effect.fail('inner failure') }))
  if (caught) innerExit = (yield* Effect.exit(inner))._tag
  else yield* inner
  return yield* TxRef.get(ref)
 })))
 return {caught, innerExit, wholeExit:wholeExit._tag, result:wholeExit._tag==='Success'?wholeExit.value:null, after:yield* TxRef.get(ref)}
})
const retryCaught = Effect.gen(function* () {
 const ref = yield* TxRef.make(0)
 let runs=0, caught=0, afterHandler=0
 const result = yield* Effect.tx(Effect.gen(function* () {
  runs++
  yield* TxRef.set(ref, runs)
  if (runs===1) {
   yield* Effect.catchCause(Effect.txRetry, () => Effect.sync(() => { caught++; return 'handled' }))
   afterHandler++
  }
  return yield* TxRef.get(ref)
 }))
 return {runs,caught,afterHandler,result,after:yield* TxRef.get(ref)}
})
const payload = mutate => Effect.gen(function* () {
 const original={n:0}
 const ref=yield* TxRef.make(original)
 const wholeExit=yield* Effect.exit(Effect.tx(Effect.gen(function* () {
  if(mutate) { const value=yield* TxRef.get(ref); value.n=1 }
  else yield* TxRef.set(ref,{n:1})
  yield* Effect.fail('abort')
 })))
 const after=yield* TxRef.get(ref)
 return {mutate,wholeExit:wholeExit._tag,after:after.n,original:original.n,sameObject:after===original,version:ref.version}
})
try {
 const result = await Effect.runPromise(Effect.gen(function* () {
  return {nestedFailure:[yield* nested(true),yield* nested(false)],caughtRetry:yield* retryCaught,payloadRollback:[yield* payload(true),yield* payload(false)]}
 }))
 console.log(JSON.stringify({metadata,result}))
} finally { clearTimeout(deadline) }
