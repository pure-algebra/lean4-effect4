import { readFileSync, writeFileSync } from 'node:fs';
import assert from 'node:assert/strict';

// Read exactly the live validation block, as the repository's existing input check does.
const source = readFileSync('tools/Tools/ProofGraphView.js', 'utf8');
const begin = source.indexOf('// pg-validate:begin');
const end = source.indexOf('// pg-validate:end');
assert(begin >= 0 && end > begin);
const validatePlan = new Function(`${source.slice(begin, end)}\nreturn validatePlan;`)();
const node = (name, nearest) => ({ name, status: 'proved', statement: '', module: 'Probe',
  axioms: [], placement: null, restsOn: [], broughtIn: { nearest, lemmas: 0, definitions: 0 } });
const report = (nodes) => ({ concepts: [], plan: { nodes, requirements: [], next: [], unplacedGoals: [] } });
const cases = {
  diamond: report([node('A', ['B', 'C']), node('B', ['D']), node('C', ['D']), node('D', [])]),
  cycle: report([node('A', ['B']), node('B', ['A'])]),
  selfLoop: report([node('A', ['A'])]),
  missing: report([node('A', ['Missing'])])
};
const results = Object.fromEntries(Object.entries(cases).map(([name, value]) => [name, validatePlan(value)]));
assert.deepEqual(results.diamond, []);
assert.deepEqual(results.cycle, []);
assert.deepEqual(results.selfLoop, []);
assert(results.missing.some((x) => x.includes('Missing')));
// An independent topological count shows the extra premise the drawing needs.
const visited = (nodes) => {
  const waiting = new Map(nodes.map((n) => [n.name, new Set(n.broughtIn.nearest)]));
  let count = 0;
  while (waiting.size) {
    const ready = [...waiting].filter(([, parents]) => parents.size === 0).map(([name]) => name);
    if (!ready.length) break;
    for (const name of ready) {
      waiting.delete(name); count++;
      for (const parents of waiting.values()) parents.delete(name);
    }
  }
  return count;
};
assert.equal(visited(cases.diamond.plan.nodes), 4);
assert.equal(visited(cases.cycle.plan.nodes), 0);
const output = { nodeVersion: process.version, validation: results,
  visited: { diamond: 4, cycle: 0 },
  limit: 'Only input validation is executed; no browser layout or current generated cycle is claimed.' };
writeFileSync(new URL('./proof-input-output.json', import.meta.url), JSON.stringify(output, null, 2) + '\n');
console.log(JSON.stringify(output, null, 2));
