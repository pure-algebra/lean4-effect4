import {readFileSync,writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
const base='/Users/pooks/Dev/lean4-effect4';
const sourcePath=base+'/tools/Tools/ProofGraphView.js';
const reportPath=base+'/.lake/gen/semantics-report/semantics.json';
const source=readFileSync(sourcePath,'utf8');
const report=JSON.parse(readFileSync(reportPath,'utf8'));
const validatePlan=new Function(source.slice(source.indexOf('// pg-validate:begin'),source.indexOf('// pg-validate:end'))+'\nreturn validatePlan;')();
// The actual pure model-building block from the view, ending before DOM controls.
const start=source.indexOf('const conceptIds =');
const end=source.indexOf('// ---------------------------------------------------------------- the controls');
if(start<0||end<start)throw Error('model markers absent');
const build=new Function('report','areaRows','const plan=report.plan; const short=(n)=>n.split(".").pop();\n'+source.slice(start,end)+'\nreturn {nodes:nodes.size};');
const rWithTop=(r)=>r.plan.requirements.find(q=>q.top.length);
const nWithNear=(r)=>r.plan.nodes.find(n=>n.broughtIn.nearest.length);
const tests=[
 ['positive untouched',()=>{}],
 ['positive empty edge list',r=>{nWithNear(r).broughtIn.nearest=[];}],
 ['negative unknown string',r=>{nWithNear(r).broughtIn.nearest.push('Missing.Proof');}],
 ['requirement top uses known string',r=>{const q=rWithTop(r);q.top[0]=q.top[0].name;}],
 ['nearest edge uses known object',r=>{const n=nWithNear(r);n.broughtIn.nearest[0]={name:n.broughtIn.nearest[0]};}],
];
const results=tests.map(([label,mutate])=>{const r=structuredClone(report);mutate(r);const problems=validatePlan(r);let model;
if(!problems.length){try{model={ok:true,...build(r,[])};}catch(e){model={ok:false,error:String(e)};}}
return {label,problems,model};});
if(results[0].problems.length||!results[0].model?.ok||!results[1].model?.ok||!results[2].problems.length)throw Error('control failed');
if(results.slice(3).some(r=>r.problems.length||r.model?.ok))throw Error('expected malformed-shape reproduction changed');
const sha=p=>createHash('sha256').update(readFileSync(p)).digest('hex');
const out={runtime:process.version,sourcePath,sourceSha256:sha(sourcePath),reportPath,reportSha256:sha(reportPath),results,scope:'Actual validator and actual pure model-building source extracted. No DOM execution, Lean execution, kernel or report-exporter defect asserted.'};
writeFileSync('/private/tmp/codex-effect4-overnight-monitor/2026-10-05-proof-scouting-followup/reference-shapes.json',JSON.stringify(out,null,2)+'\n');
console.log(JSON.stringify(out,null,2));
