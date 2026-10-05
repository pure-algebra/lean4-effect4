import { readFileSync, writeFileSync } from 'node:fs'
import { createHash } from 'node:crypto'
import assert from 'node:assert/strict'

const root = process.argv[2]
const output = process.argv[3]
const version = JSON.parse(readFileSync(`${root}/package.json`, 'utf8')).version
const [Effect, Fiber, Queue, Option] = await Promise.all(
  ['Effect', 'Fiber', 'Queue', 'Option'].map(name => import(`${root}/dist/${name}.js`))
)
const settle = Effect.gen(function* () {
  for (let i = 0; i < 8; i++) yield* Effect.yieldNow
})
const option = value => Option.isSome(value) ? { some: value.value } : { none: true }
const single = (strategy, capacity, peeking = false) => Effect.gen(function* () {
  const q = yield* Queue[strategy](capacity)
  const log = []
  const t = yield* Effect.forkChild(Effect.gen(function* () {
    log.push(['received', yield* (peeking ? Queue.peek(q) : Queue.take(q))])
  }))
  yield* settle
  log.push(['before-offer'])
  const accepted = yield* Queue.offer(q, 7)
  log.push(['offer-return', accepted])
  const immediateSize = yield* Queue.size(q)
  const immediateLog = [...log]
  yield* settle
  const afterSettle = { size: yield* Queue.size(q), log: [...log], receiverDone: t.pollUnsafe() !== undefined }
  let afterFlush = null
  if (strategy === 'sliding' && capacity === 0 && typeof Queue.flush === 'function') {
    yield* Queue.flush(q)
    afterFlush = { size: yield* Queue.size(q), log: [...log], receiverDone: t.pollUnsafe() !== undefined }
  }
  yield* Fiber.interrupt(t)
  return { accepted, immediateSize, immediateLog, afterSettle, afterFlush }
})
const main = Effect.gen(function* () {
  const noReceiver = yield* Queue.dropping(0)
  const noReceiverAccepted = yield* Queue.offer(noReceiver, 7)
  const droppingSingle = yield* single('dropping', 0)
  const droppingPeek = yield* single('dropping', 0, true)
  const droppingBatch = yield* Effect.gen(function* () {
    const q = yield* Queue.dropping(0)
    const t = yield* Effect.forkChild(Queue.take(q))
    yield* settle
    const remaining = yield* Queue.offerAll(q, [7])
    const beforeCancel = { size: yield* Queue.size(q), receiverDone: t.pollUnsafe() !== undefined }
    yield* Fiber.interrupt(t)
    yield* settle
    return { remaining, beforeCancel, afterCancelSize: yield* Queue.size(q), laterPoll: option(yield* Queue.poll(q)) }
  })
  const slidingSingleZero = yield* single('sliding', 0)
  const slidingBatchZero = yield* Effect.gen(function* () {
    const q = yield* Queue.sliding(0)
    const t = yield* Effect.forkChild(Queue.take(q))
    yield* settle
    const remaining = yield* Queue.offerAll(q, [7])
    yield* settle
    const result = { remaining, size: yield* Queue.size(q), receiverDone: t.pollUnsafe() !== undefined }
    yield* Fiber.interrupt(t)
    return result
  })
  const slidingSingleOne = yield* single('sliding', 1)
  return { noReceiverAccepted, droppingSingle, droppingPeek, droppingBatch, slidingSingleZero, slidingBatchZero, slidingSingleOne }
})
const result = await Effect.runPromise(main)
const receipt = { entry: 'dist', importedHashes: Object.fromEntries(['Queue', 'Effect', 'Fiber', 'Option'].map(name => [name, createHash('sha256').update(readFileSync(`${root}/dist/${name}.js`)).digest('hex')])), version, runtime: `Bun ${Bun.version}`, root, observation: 'Default runtime; eight explicit yields settle each receiver; finite schedules only.',
  sourceHashes: Object.fromEntries(['Queue', 'Effect', 'Fiber', 'internal/effect'].map(name => [name, createHash('sha256').update(readFileSync(`${root}/src/${name}.ts`)).digest('hex')])), result }
writeFileSync(output, JSON.stringify(receipt, null, 2) + '\n')
assert.equal(result.noReceiverAccepted, false)
assert.equal(result.droppingSingle.accepted, version === '4.0.1')
assert.equal(result.droppingSingle.afterSettle.receiverDone, version === '4.0.1')
assert.equal(result.droppingPeek.accepted, version === '4.0.1')
assert.equal(result.droppingPeek.afterSettle.size, version === '4.0.1' ? 1 : 0)
assert.deepEqual(result.droppingBatch.remaining, [])
assert.equal(result.droppingBatch.beforeCancel.receiverDone, false)
assert.equal(result.droppingBatch.afterCancelSize, 1)
assert.deepEqual(result.droppingBatch.laterPoll, { some: 7 })
assert.equal(result.slidingSingleZero.accepted, true)
assert.equal(result.slidingSingleZero.afterSettle.receiverDone, false)
assert.equal(result.slidingSingleZero.afterSettle.size, 1)
assert.equal(result.slidingBatchZero.size, 0)
assert.equal(result.slidingBatchZero.receiverDone, false)
assert.equal(result.slidingSingleOne.afterSettle.receiverDone, true)
assert.equal(result.slidingSingleOne.afterSettle.size, 0)
if (version === '4.0.1') {
  assert.deepEqual(result.droppingSingle.immediateLog, [['before-offer'], ['received', 7], ['offer-return', true]])
  assert.equal(result.slidingSingleZero.afterFlush.receiverDone, true)
  assert.equal(result.slidingSingleZero.afterFlush.size, 0)
}
console.log(JSON.stringify({ version, assertions: version === '4.0.1' ? 19 : 16, passed: true, output, result }))
