import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
const packageRoot = process.argv[2];
if (!packageRoot) throw new Error('Pass the installed effect package directory.');
const load = name => import(pathToFileURL(`${packageRoot}/dist/${name}.js`).href);
const [Effect, Fiber, Scope, Exit, Deferred, Ref] = await Promise.all(
  ['Effect', 'Fiber', 'Scope', 'Exit', 'Deferred', 'Ref'].map(load));
const pin = JSON.parse(readFileSync(`${packageRoot}/package.json`, 'utf8'));
if (pin.version !== '4.0.0-rc.112') throw new Error(`Expected rc.112, found ${pin.version}`);
const inspect = fiber => ({ observers: fiber._observers.length, running: fiber._running,
  exit: fiber.pollUnsafe()?._tag ?? null, deferred: fiber._deferredInterrupt });
const join = Effect.runFork(Effect.withFiber(self => Fiber.await(self)));
const countdown = Effect.runFork(Effect.withFiber(self => Fiber.awaitAll([self])));
const scope = Scope.makeUnsafe();
const link = Effect.runFork(Effect.withFiber(self => { Fiber.runIn(self, scope); return Effect.never; }));
const closedScope = Scope.makeUnsafe();
Effect.runSync(Scope.close(closedScope, Exit.succeed(undefined)));
const closedLink = Effect.runFork(Effect.withFiber(self => { Fiber.runIn(self, closedScope); return Effect.never; }));
const selfInterrupt = Effect.runFork(Effect.withFiber(self => Fiber.interrupt(self)));
const awaitedPeer = Effect.runFork(Effect.never);
const countdownCallback = Effect.runFork(Effect.withFiber(self => Fiber.awaitAll([awaitedPeer, self])));
awaitedPeer.interruptUnsafe(77);
const cases = { countdownCallback: inspect(countdownCallback), join: inspect(join), countdown: inspect(countdown), openLink: inspect(link),
  closedLink: inspect(closedLink), selfInterrupt: inspect(selfInterrupt) };
const byHandle = Effect.gen(function*() {
  const d = yield* Deferred.make();
  const log = yield* Ref.make(0);
  const child = yield* Effect.forkChild(Effect.gen(function*() {
    const me = yield* Deferred.await(d);
    yield* Fiber.interrupt(me);
    yield* Ref.update(log, n => n + 1);
    return 1;
  }));
  yield* Deferred.succeed(d, child);
  const exit = yield* Fiber.await(child);
  return { child: exit._tag, reasons: exit._tag === 'Failure' ? exit.cause.reasons.map(r => r._tag) : [],
    log: yield* Ref.get(log) };
});
const retained = await Effect.runPromise(byHandle);
console.log(JSON.stringify({ version: pin.version, cases, retained }, null, 2));
if (cases.join.observers !== 1 || cases.countdown.observers !== 1 || cases.openLink.observers !== 1 || cases.countdownCallback.observers !== 1)
  throw new Error('Self-target observer registration was not retained.');
if (cases.closedLink.exit !== 'Failure' || cases.selfInterrupt.exit !== 'Failure')
  throw new Error('Self-target interruption did not exit with Failure.');
if (retained.child !== 'Failure' || !retained.reasons.includes('Interrupt') || retained.log !== 0)
  throw new Error('The retained CE046 program did not exit interrupted before its log write.');
