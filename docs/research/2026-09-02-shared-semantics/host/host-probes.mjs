import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import * as Effect from '/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/dist/Effect.js';
import * as Scope from '/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/dist/Scope.js';
import * as Exit from '/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/dist/Exit.js';
const results = [];
const version = JSON.parse(readFileSync('/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/package.json')).version;
assert.equal(version, '4.0.0-rc.112');
const trace = [];
const computation = Effect.gen(function* () {
  trace.push('start');
  try { yield* Effect.fail('typed-failure'); }
  finally { trace.push('js-finally'); }
});
assert.deepEqual(trace, []);
const failure = await Effect.runPromiseExit(computation);
assert.equal(failure._tag, 'Failure');
assert.deepEqual(trace, ['start']);
results.push({case:'generator finally on yielded failure', trace:[...trace], exit:failure._tag});
const resourceTrace = [];
const resource = Effect.scoped(Effect.gen(function* () {
  yield* Effect.acquireRelease(Effect.sync(() => {resourceTrace.push('acquire'); return 'r';}),
    (_r, exit) => Effect.sync(() => resourceTrace.push('release:' + exit._tag)));
  yield* Effect.sync(() => resourceTrace.push('body-write'));
  yield* Effect.fail('body-failure');
}));
const resourceExit = await Effect.runPromiseExit(resource);
assert.equal(resourceExit._tag, 'Failure');
assert.deepEqual(resourceTrace, ['acquire','body-write','release:Failure']);
results.push({case:'scoped release sees failure after body state change', trace:resourceTrace});
const order = [];
await Effect.runPromise(Effect.gen(function* () {
  const scope = yield* Scope.make();
  yield* Scope.addFinalizer(scope, Effect.sync(() => order.push('first')));
  yield* Scope.addFinalizer(scope, Effect.sync(() => order.push('second')));
  yield* Scope.close(scope, Exit.void);
  yield* Scope.close(scope, Exit.void);
}));
assert.deepEqual(order, ['second','first']);
results.push({case:'LIFO close then repeated close', trace:order});
const abortTrace = [];
const abort = new AbortController();
abort.signal.addEventListener('abort', () => abortTrace.push('abort-event'));
abort.abort('first-reason'); abort.abort('second-reason');
assert.deepEqual(abortTrace,['abort-event']);
assert.equal(abort.signal.reason,'first-reason');
results.push({case:'abort reason stable and event occurs once', trace:abortTrace,reason:abort.signal.reason});
let desired;
const stream = new ReadableStream({ start(controller) {
  controller.enqueue('a'); controller.enqueue('b'); controller.enqueue('c');
  desired = controller.desiredSize; controller.close();
}}, {highWaterMark:1,size:()=>1});
assert.equal(desired,-2);
await stream.cancel();
results.push({case:'high water mark is not a hard queue cap',highWaterMark:1,enqueued:3,desiredSize:desired});
console.log(JSON.stringify({node:process.version,effect:version,results},null,2));
