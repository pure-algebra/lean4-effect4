import {readFileSync} from 'node:fs';
import {parseTypeScript,childNodes} from '/Users/pooks/.codex/worktrees/module-semaphore/lean4-effect4/ts/eff/ingest/oxc.ts';
const root='/Users/pooks/.codex/worktrees/module-semaphore/lean4-effect4';
const report=JSON.parse(readFileSync(root+'/docs/research/2026-10-08-module-survey.json','utf8'));
console.log(JSON.stringify({counts:report.counts,topHelpers:report.sharedHelpers.slice(0,12).map(x=>({target:x.target,moduleCount:x.modules.length,sites:x.sites})),externalRelative:report.edges.filter(e=>!e.internal&&e.to.startsWith('.')).slice(0,5)}));
const counts={runtimeTS:0,namedClass:0,classImportShadow:0,switchImportShadow:0,computedKeysWithCalls:0,exportDefaults:0};
const examples={};
function mark(kind,file,node,source) {counts[kind]++; (examples[kind]??=[]).length<5&&examples[kind].push({file,start:node.start,text:source.slice(node.start,node.end).slice(0,200)});}
for (const m of report.modules) {
 const source=readFileSync(root+'/vendor/effect-4.0.1/src/'+m.file,'utf8');
 const {program}=parseTypeScript(m.file,source);
 const imports=new Set(program.body.filter(n=>n.type==='ImportDeclaration'&&n.importKind!=='type').flatMap(n=>n.specifiers.filter(s=>s.importKind!=='type').map(s=>s.local.name)));
 function bindings(n){if(!n)return [];if(n.type==='Identifier')return [n.name];if(n.type==='VariableDeclaration')return n.declarations.flatMap(d=>bindings(d.id));if(n.type==='FunctionDeclaration'||n.type==='ClassDeclaration')return bindings(n.id);if(n.type==='ObjectPattern')return n.properties.flatMap(p=>bindings(p.value??p.argument));if(n.type==='ArrayPattern')return n.elements.flatMap(bindings);if(n.type==='AssignmentPattern')return bindings(n.left);return [];}
 function hasCall(n){return n&&((n.type==='CallExpression'||n.type==='NewExpression')||childNodes(n).some(hasCall));}
 function walk(n){
  if(['TSEnumDeclaration','TSImportEqualsDeclaration','TSExportAssignment'].includes(n.type)||n.type==='TSModuleDeclaration'&&n.kind!=='namespace')mark('runtimeTS',m.file,n,source);
  if(n.type==='ClassExpression'&&n.id){mark('namedClass',m.file,n,source);if(imports.has(n.id.name))mark('classImportShadow',m.file,n,source);}
  if(n.type==='SwitchStatement'&&n.cases.flatMap(c=>c.consequent).flatMap(bindings).some(name=>imports.has(name)))mark('switchImportShadow',m.file,n,source);
  if(['MethodDefinition','PropertyDefinition','Property'].includes(n.type)&&n.computed&&hasCall(n.key))mark('computedKeysWithCalls',m.file,n,source);
  if(n.type==='ExportDefaultDeclaration'&&['FunctionDeclaration','ClassDeclaration'].includes(n.declaration?.type))mark('exportDefaults',m.file,n,source);
  for(const c of childNodes(n))walk(c);
 }
 walk(program);
}
console.log(JSON.stringify({counts,examples}));
