import { readFileSync } from 'node:fs';
const root = process.argv[2];
const report = JSON.parse(readFileSync(process.argv[3], 'utf8'));
const source = readFileSync(`${root}/tools/Tools/ProofGraphView.js`, 'utf8');
const v0 = source.indexOf('// pg-validate:begin'), v1 = source.indexOf('// pg-validate:end');
const validate = new Function(`${source.slice(v0, v1)}\nreturn validatePlan;`)();
const m0 = source.indexOf('const conceptIds ='), m1 = source.indexOf('// ---------------------------------------------------------------- the controls');
if (v0 < 0 || v1 < v0 || m0 < 0 || m1 < m0) throw new Error('source extraction markers missing');
const make = new Function('report', 'areaRows', 'short', `const plan = report.plan;\n${source.slice(m0, m1)}\nreturn {nodes};`);
const model = (r) => make(r, [], (n) => n.split('.').pop()).nodes;
const own = validate(report);
if (own.length) throw new Error(`base report invalid: ${JSON.stringify(own)}`);
const claims = new Map();
for (const c of report.claims) {
 const s = c.status, w = s.witness || s.goal || (s.counterexample && s.counterexample.witness);
 if (w && w.name && !claims.has(w.name)) claims.set(w.name,c);
}
const nodes=model(report), affected=[];
for (const n of report.plan.nodes) {
 const c=claims.get(n.name);
 const expected=(c&&c.concept) || (n.placement&&n.placement.concept);
 if (expected && nodes.get(n.name).concept !== expected) affected.push({name:n.name,kind:n.kind,status:n.status,expected,actual:nodes.get(n.name).concept,requirement:n.placement?.requirement});
}
const sample=report.plan.nodes.find(n=>n.kind==='goal'&&n.placement&&!claims.has(n.name));
if(!sample) throw new Error('retained report lacks exact goal witness');
const tests=[];
const copy=()=>JSON.parse(JSON.stringify(report));
let r=copy();r.plan.nodes.find(n=>n.name===sample.name).placement.concept='Unknown.concept';
tests.push({name:'unknown concept refused',passed:validate(r).some(x=>x.includes('Unknown.concept')),messages:validate(r)});
r=copy();r.plan.nodes.find(n=>n.name===sample.name).placement.requirement='Unknown.requirement';
tests.push({name:'unknown requirement refused',passed:validate(r).some(x=>x.includes('Unknown.requirement')),messages:validate(r)});
r=copy();r.plan.nodes.find(n=>n.name===sample.name).broughtIn.nearest.push('Unknown.nearest');
tests.push({name:'known reference refusal retained',passed:validate(r).some(x=>x.includes('Unknown.nearest')),messages:validate(r)});
const claimed=report.plan.nodes.find(n=>claims.has(n.name));
tests.push({name:'named claim positive',passed:nodes.get(claimed.name).concept===claims.get(claimed.name).concept,nameOfNode:claimed.name});
const restUnchanged=report.plan.nodes.every(n=>JSON.stringify(nodes.get(n.name).restsOn)===JSON.stringify(n.restsOn)&&JSON.stringify(nodes.get(n.name).out)===JSON.stringify(n.broughtIn.nearest)&&nodes.get(n.name).status===n.status);
tests.push({name:'statuses and measured edges retained',passed:restUnchanged});
const result={sourceRoot:root,reportNodes:report.plan.nodes.length,baseValidatorAccepted:own.length===0,lostExplicitPlacementCount:affected.length,affected,controls:tests,pass:affected.length===0&&tests.every(t=>t.passed)};
console.log(JSON.stringify(result,null,2));
if(!result.pass)process.exitCode=1;
