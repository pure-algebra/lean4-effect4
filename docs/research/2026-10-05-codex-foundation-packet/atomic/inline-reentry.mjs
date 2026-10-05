import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
const packages = [
  '/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect',
  '/Users/pooks/.bun/install/cache/effect@4.0.1@@@1'
];
const assert = (test, label) => { if (!test) throw new Error(label); };
const output = [];
for (const dir of packages) {
  const Effect = await import(`${dir}/src/Effect.ts`);
  const Ref = await import(`${dir}/src/Ref.ts`);
  const Deferred = await import(`${dir}/src/Deferred.ts`);
  const Scheduler = await import(`${dir}/src/Scheduler.ts`);
  const version = JSON.parse(readFileSync(`${dir}/package.json`, 'utf8')).version;
  const cases = [];
  for (const signalBetweenWrites of [false, true]) {
    let scheduled = 0;
    let yieldChecks = 0;
    const scheduler = {
      executionMode: 'sync',
      shouldYield: () => { yieldChecks++; return false; },
      makeDispatcher: () => ({
        scheduleTask: () => { scheduled++; throw new Error('Unexpected scheduled task'); },
        flush: () => {}
      })
    };
    const run = effect => Effect.runFork(effect, { scheduler });
    const get = effect => {
      const exit = run(effect).pollUnsafe();
      assert(exit?._tag === 'Success', 'Expected immediate success');
      return exit.value;
    };
    const cell = get(Ref.make(0));
    const gate = get(Deferred.make());
    const observer = run(Effect.flatMap(Deferred.await(gate), () => Ref.get(cell)));
    assert(observer.pollUnsafe() === undefined, 'Observer must be registered before writer');
    const writer = Effect.gen(function*() {
      yield* Ref.set(cell, 1);
      if (signalBetweenWrites) yield* Deferred.succeed(gate, undefined);
      yield* Ref.set(cell, 2);
      if (!signalBetweenWrites) yield* Deferred.succeed(gate, undefined);
    });
    get(Effect.provideService(Effect.uninterruptible(writer), Scheduler.PreventSchedulerYield, true));
    const observed = observer.pollUnsafe();
    assert(observed?._tag === 'Success', 'Observer completes inline');
    assert(observed.value === (signalBetweenWrites ? 1 : 2), 'Unexpected observed cell');
    const finalValue = get(Ref.get(cell));
    assert(finalValue === 2 && scheduled === 0, 'No scheduled task and final cell two');
    cases.push({ signalBetweenWrites, observed: observed.value, finalValue, scheduled, yieldChecks });
  }
  const sources = Object.fromEntries(['Effect.ts','Ref.ts','Deferred.ts','Scheduler.ts','internal/effect.ts'].map(name => [name, createHash('sha256').update(readFileSync(`${dir}/src/${name}`)).digest('hex')]));
  output.push({ version, package:dir, cases, sources });
}
console.log(JSON.stringify({runtime:`bun ${Bun.version}`, question:'Do masking and prevented scheduler yields exclude inline entry into another fiber?', results:output, conclusion:'No. A Deferred completion between two ordinary Ref writes lets the registered fiber read the intermediate value. The after-write signal is the positive control.', scope:'Four finite actual runtime cases, no tx wrapper or Lean implementation claim. No task is flushed or scheduled. No compiler/typecheck claim.'}, null, 2));
