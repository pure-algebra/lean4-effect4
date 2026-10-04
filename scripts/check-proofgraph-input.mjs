// Controls for the proof graph view's input check (validatePlan in tools/Tools/ProofGraphView.js).
// The view draws nothing from a report that fails the check; it shows the problems instead. This
// script runs the same block, read from the view's source between its markers, on the generated
// semantics report and on broken copies of it:
//
// - the generated report passes;
// - a report with no plan, a plan whose nodes are not a list, a node whose nearest node is unknown,
//   and a requirement whose top node is unknown each fail, with a problem naming the cause.
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
console.log(`PASS check-proofgraph-input: the generated report passes (${nodes.length} nodes, ${report.plan.requirements.length} requirements); ${cases.length} broken copies refused`);
