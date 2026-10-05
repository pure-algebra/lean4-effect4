import { readFileSync, writeFileSync } from 'node:fs'
import { createHash } from 'node:crypto'
import assert from 'node:assert/strict'
const root = process.argv[2], output = process.argv[3]
const { Effect: E, Fiber: F } = await import(`${root}/dist/index.js`)
const version = JSON.parse(readFileSync(`${root}/package.json`, 'utf8')).version
const getter = E.uninterruptibleMask(restore => E.succeed(restore))
const native = body => E.uninterruptibleMask(body)
const printed = body => E.flatMap(getter, saved => E.uninterruptible(body(saved)))
const flag = E.withFiber(f => E.succeed(f.interruptible))
const exit = f => {
  const x = f.pollUnsafe()
  return x ? { tag: x._tag, value: x._tag === 'Success' ? x.value : null,
    reasons: x._tag === 'Failure' ? x.cause.reasons.map(r => r._tag) : [] } : { tag: 'Pending' }
}
const defaultCases = {}
for (const [name, mask] of [['native', native], ['printed', printed]]) {
  defaultCases[name] = {
    bodyMaskedControl: await E.runPromise(mask(() => flag)),
    explicitInterruptibleOutsideRestore: await E.runPromise(mask(() => E.interruptible(flag))),
    restoredOpenControl: await E.runPromise(mask(restore => restore(flag))),
    explicitUninterruptibleInsideRestore: await E.runPromise(mask(restore => restore(E.uninterruptible(flag)))),
    maskedIncomingControl: await E.runPromise(E.uninterruptible(mask(restore => restore(flag))))
  }
  assert.deepEqual(defaultCases[name], { bodyMaskedControl: false, explicitInterruptibleOutsideRestore: true,
    restoredOpenControl: true, explicitUninterruptibleInsideRestore: false, maskedIncomingControl: false })
}
class Manual {
  executionMode = 'sync'; tasks = []; checks = []; subject = undefined; yielded = false
  constructor(cut = null) { this.cut = cut }
  shouldYield(f) {
    this.subject ??= f.id
    if (f.id === this.subject) {
      this.checks.push({ op: f.currentOpCount, interruptible: f.interruptible, pending: !!f._interruptedCause })
      if (!this.yielded && this.cut === f.currentOpCount) { this.yielded = true; return true }
    }
    return false
  }
  makeDispatcher() { return { scheduleTask: (run, priority) => this.tasks.push({run, priority}), flush: () => this.drain() } }
  run(e) { return E.runFork(e, { scheduler: this }) }
  drain() { let n = 0; while (this.tasks.length) { assert(++n <= 50); this.tasks.sort((a,b) => a.priority-b.priority); this.tasks.shift().run() } }
}
const counted = (mask, incomingMasked, mapped) => {
  const h = new Manual()
  let program = mask(() => mapped ? E.map(E.succeed(1), x => x + 1) : E.succeed(1))
  if (incomingMasked) program = E.uninterruptible(program)
  const f = h.run(program)
  assert.equal(exit(f).tag, 'Success')
  assert.equal(h.tasks.length, 0)
  return { checks: h.checks, schedulerCheckCount: h.checks.length, finalOpCount: f.currentOpCount, exit: exit(f) }
}
const counts = {}
for (const [name, mask] of [['native',native],['printed',printed]]) {
  counts[name] = { open: counted(mask,false,false), masked: counted(mask,true,false), mappedBody: counted(mask,false,true) }
  assert.equal(counts[name].open.schedulerCheckCount, name === 'native' ? 2 : 5)
  assert.equal(counts[name].masked.schedulerCheckCount, name === 'native' ? 3 : 6)
}
const cancellationCase = (name, mask, cut, cancel, incomingMasked = false) => {
  const h = new Manual(cut), events = []
  let program = mask(() => E.sync(() => { events.push('body'); return 7 }))
  if (incomingMasked) program = E.uninterruptible(program)
  const f = h.run(program)
  assert.equal(exit(f).tag, 'Pending')
  const atCut = { interruptible: f.interruptible, pending: !!f._interruptedCause, events: [...events] }
  const stopper = cancel ? h.run(F.interrupt(f)) : null
  const afterRequest = { interruptible: f.interruptible, pending: !!f._interruptedCause, exit: exit(f) }
  h.drain()
  if (stopper) assert.equal(exit(stopper).tag, 'Success')
  assert.equal(exit(f).tag, cancel ? 'Failure' : 'Success')
  if (cancel) assert(exit(f).reasons.includes('Interrupt'))
  const shouldEnter = !cancel || name.startsWith('native') || incomingMasked
  assert.equal(events.includes('body'), shouldEnter)
  assert.equal(h.tasks.length, 0)
  return { name, cut, cancel, incomingMasked, atCut, afterRequest, events, exit: exit(f), checks: h.checks }
}
const cancellation = [
  cancellationCase('printed-getter-pop',printed,3,true),
  cancellationCase('printed-getter-pop-control',printed,3,false),
  cancellationCase('native-before-body',native,2,true),
  cancellationCase('native-before-body-control',native,2,false),
  cancellationCase('printed-open-window',printed,4,true),
  cancellationCase('printed-open-window-control',printed,4,false),
  cancellationCase('printed-masked-getter-pop',printed,4,true,true),
  cancellationCase('printed-masked-getter-pop-control',printed,4,false,true)
]
const receipt = { version, runtime: `Bun ${Bun.version}`, root, entry: 'dist/index.js',
  defaultCases, counts, cancellation,
  evidence: 'Finite default-runtime flag controls; separate custom scheduler loop checks and forced-yield cancellation cases. No Lean execution.',
  hashes: Object.fromEntries(['package.json','dist/index.js','dist/internal/effect.js','dist/internal/core.js','src/internal/effect.ts','src/internal/core.ts'].map(p=>[p,createHash('sha256').update(readFileSync(`${root}/${p}`)).digest('hex')])) }
writeFileSync(output, JSON.stringify(receipt,null,2)+'\n')
console.log(JSON.stringify({ version, defaultCases, counts: Object.fromEntries(Object.entries(counts).map(([k,v])=>[k,Object.fromEntries(Object.entries(v).map(([n,c])=>[n,{schedulerCheckCount:c.schedulerCheckCount,finalOpCount:c.finalOpCount}]))])),
  cancellation: cancellation.map(c=>({name:c.name,atCut:c.atCut,afterRequest:c.afterRequest,events:c.events,exit:c.exit})), output }))
