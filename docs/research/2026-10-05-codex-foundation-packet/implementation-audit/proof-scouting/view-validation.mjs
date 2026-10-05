import {readFileSync,writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
const root='/Users/pooks/Dev/lean4-effect4';
const sourcePath=root+'/tools/Tools/ProofGraphView.js';
const reportPath=root+'/.lake/gen/semantics-report/semantics.json';
const source=readFileSync(sourcePath,'utf8');
const report=JSON.parse(readFileSync(reportPath,'utf8'));
const begin=source.indexOf('// pg-validate:begin'),end=source.indexOf('// pg-validate:end');
if(begin<0||end<begin)throw Error('validator markers missing');
const validatePlan=new Function(source.slice(begin,end)+'\nreturn validatePlan;')();
const hash=(p)=>createHash('sha256').update(readFileSync(p)).digest('hex');
const cases=[
 ['positive untouched report',r=>{}],
 ['negative unknown nearest',r=>{r.plan.nodes[0].broughtIn.nearest.push('Missing.Proof');}],
 ['missing statement',r=>{delete r.plan.nodes[0].statement;}],
 ['missing axioms',r=>{delete r.plan.nodes[0].axioms;}],
 ['report diagnostic',r=>{r.errors=['scout injected diagnostic'];}],
 ['missing nearest',r=>{delete r.plan.nodes[0].broughtIn.nearest;}],
 ['missing open parts',r=>{delete r.plan.requirements[0].openParts;}]
];
const results=cases.map(([label,mutate])=>{const r=structuredClone(report);mutate(r);return {label,problems:validatePlan(r)};});
if(results[0].problems.length||!results[1].problems.some(s=>s.includes('Missing.Proof')))throw Error('positive or negative control failed');
const out={runtime:process.version,sourcePath,sourceSha256:hash(sourcePath),reportPath,reportSha256:hash(reportPath),sourceReportKeys:Object.keys(report),node:report.plan.nodes[0].name,results,scope:'Actual extracted validator; no UI rendering, no Lean run, no assertion about compiled theorem soundness.'};
writeFileSync('/private/tmp/codex-effect4-overnight-monitor/2026-10-05-proof-scouting/view-validation.json',JSON.stringify(out,null,2)+'\n');
console.log(JSON.stringify({node:out.node,sourceReportKeys:out.sourceReportKeys,results},null,2));
