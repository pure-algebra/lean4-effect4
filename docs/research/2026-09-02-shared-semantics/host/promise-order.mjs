import assert from 'node:assert/strict';

async function trial(extraReaction) {
  const trace = [];
  const source = Promise.resolve('same result');
  const candidate = extraReaction ? source.then(value => value) : source;
  candidate.then(value => trace.push('result:' + value));
  Promise.resolve().then(() => trace.push('marker'));
  await new Promise(setImmediate);
  return trace;
}

const direct = await trial(false);
const extraReaction = await trial(true);
assert.deepEqual(direct, ['result:same result', 'marker']);
assert.deepEqual(extraReaction, ['marker', 'result:same result']);
console.log(JSON.stringify({node: process.version, direct, extraReaction}, null, 2));
