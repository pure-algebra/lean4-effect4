// Controls for the proof graph view's input check (validatePlan in tools/Tools/ProofGraphView.js).
// The view draws nothing from a report that fails the check; it shows the problems instead. This
// script runs the same block, read from the view's source between its markers, on the generated
// semantics report and on broken copies of it:
//
// - the generated report passes;
// - a report with no plan, a plan whose nodes are not a list, a node whose nearest node is unknown,
//   and a requirement whose top node is unknown each fail, with a problem naming the cause;
// - a copy that lacks one field the drawings read fails, with a problem naming the field: an
//   absent list is not an empty one (Codex's dogfooding review, 2026-10-05);
// - a copy with that field present and empty passes;
// - a reference in the other shape fails: a requirement's top node given as a bare name, and a
//   node's nearest node given as an object. The view reads each field in one shape only.
//
// Usage: node scripts/check-proofgraph-input.mjs [semantics.json]
import { readFileSync } from 'node:fs';

const source = readFileSync('tools/Tools/ProofGraphView.js', 'utf8');
const begin = source.indexOf('// pg-validate:begin');
const end = source.indexOf('// pg-validate:end');
if (begin < 0 || end < begin) throw new Error('check-proofgraph-input: the view has no pg-validate block');
const validatePlan = new Function(`${source.slice(begin, end)}\nreturn validatePlan;`)();

const path = process.argv[2] || '.lake/gen/semantics-report/semantics.json';
const report = JSON.parse(readFileSync(path, 'utf8'));
const fail = (why) => { console.error(`FAIL check-proofgraph-input: ${why}`); process.exit(1); };

const own = validatePlan(report);
if (own.length) fail(`the generated report fails the view's check: ${own.slice(0, 5).join('; ')}`);
const nodes = report.plan.nodes;
const withNearest = nodes.find((n) => ((n.broughtIn || {}).nearest || []).length > 0) || nodes[0];
if (!withNearest || !report.plan.requirements.length) fail('the generated report has no node or requirement to break');

const copy = () => JSON.parse(JSON.stringify(report));
const cases = [
  ['no plan', (r) => { delete r.plan; }, 'no plan section'],
  ['nodes not a list', (r) => { r.plan.nodes = {}; }, 'plan.nodes is not a list'],
  ['unknown nearest node', (r) => {
    const n = r.plan.nodes.find((m) => m.name === withNearest.name);
    n.broughtIn = { ...(n.broughtIn || {}), nearest: [...((n.broughtIn || {}).nearest || []), 'Unknown.nearest'] };
  }, 'Unknown.nearest'],
  ['unknown top node', (r) => {
    const q = r.plan.requirements[0];
    q.top = [...(q.top || []), { name: 'Unknown.top', status: 'proved' }];
  }, 'Unknown.top'],
];
for (const [label, mutate, expected] of cases) {
  const broken = copy();
  mutate(broken);
  const problems = validatePlan(broken);
  if (!problems.some((p) => p.includes(expected))) fail(`${label}: expected a problem naming "${expected}", got ${JSON.stringify(problems)}`);
}

// A field that the drawings read: absent, it is a problem that names it; empty, it is a value.
const node = (r) => r.plan.nodes.find((m) => m.name === withNearest.name);
const fields = [
  ["a node's statement", (r) => { delete node(r).statement; }, (r) => { node(r).statement = ''; }, 'statement is missing'],
  ["a node's module", (r) => { delete node(r).module; }, (r) => { node(r).module = ''; }, 'module is missing'],
  ["a node's axioms", (r) => { delete node(r).axioms; }, (r) => { node(r).axioms = []; }, 'axioms is missing'],
  ["a node's goals", (r) => { delete node(r).restsOn; }, (r) => { node(r).restsOn = []; }, 'goals is missing'],
  ["a node's nearest nodes", (r) => { delete node(r).broughtIn.nearest; }, (r) => { node(r).broughtIn.nearest = []; }, 'nearest nodes is missing'],
  ["a node's dependency summary", (r) => { delete node(r).broughtIn; }, (r) => { node(r).broughtIn = { nearest: [], lemmas: 0, definitions: 0 }; }, 'dependency summary is missing'],
  ["a node's count of lemmas", (r) => { delete node(r).broughtIn.lemmas; }, (r) => { node(r).broughtIn.lemmas = 0; }, 'count of lemmas is missing'],
  ["a requirement's open parts", (r) => { delete r.plan.requirements[0].openParts; }, (r) => { r.plan.requirements[0].openParts = []; }, 'open parts is missing'],
  ["a requirement's top nodes", (r) => { delete r.plan.requirements[0].top; }, (r) => { r.plan.requirements[0].top = []; }, 'top nodes is missing'],
  ["a requirement's placed nodes", (r) => { delete r.plan.requirements[0].placed; }, (r) => { r.plan.requirements[0].placed = []; }, 'placed nodes is missing'],
  ["a requirement's next goals", (r) => { delete r.plan.requirements[0].next; }, (r) => { r.plan.requirements[0].next = []; }, 'next goals is missing'],
  ["the plan's next goals", (r) => { delete r.plan.next; }, (r) => { r.plan.next = []; }, 'the next goals is missing'],
  ["the plan's unplaced goals", (r) => { delete r.plan.unplacedGoals; }, (r) => { r.plan.unplacedGoals = []; }, 'the unplaced goals is missing'],
];
for (const [label, remove, empty, expected] of fields) {
  const absent = copy();
  remove(absent);
  const problems = validatePlan(absent);
  if (!problems.some((p) => p.includes(expected))) fail(`${label} absent: expected a problem naming "${expected}", got ${JSON.stringify(problems)}`);
  const emptied = copy();
  empty(emptied);
  const none = validatePlan(emptied);
  if (none.length) fail(`${label} empty: expected no problem, got ${JSON.stringify(none.slice(0, 3))}`);
}

// A known reference in the wrong shape for its field.
const withTop = report.plan.requirements.findIndex((q) => (q.top || []).length > 0);
if (withTop < 0) fail('the generated report has no requirement with a top node to reshape');
const shapes = [
  ["a requirement's top node as a bare name", (r) => { const q = r.plan.requirements[withTop]; q.top[0] = q.top[0].name; }, 'top nodes has an entry that is not an object with a name'],
  ["a node's nearest node as an object", (r) => { const n = node(r); n.broughtIn.nearest[0] = { name: n.broughtIn.nearest[0] }; }, 'nearest nodes has an entry that is not a name'],
];
if (!(node(report).broughtIn.nearest || []).length) fail('the generated report has no nearest node to reshape');
for (const [label, mutate, expected] of shapes) {
  const reshaped = copy();
  mutate(reshaped);
  const problems = validatePlan(reshaped);
  if (!problems.some((p) => p.includes(expected))) fail(`${label}: expected a problem naming "${expected}", got ${JSON.stringify(problems)}`);
}
console.log(`PASS check-proofgraph-input: the generated report passes (${nodes.length} nodes, ${report.plan.requirements.length} requirements); ${cases.length} broken copies refused; ${fields.length} absent fields refused, and the same fields accepted when empty; ${shapes.length} references in the wrong shape refused`);
