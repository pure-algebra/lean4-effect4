from pathlib import Path
import difflib
base=Path(__file__).parent
js_path='tools/Tools/ProofGraphView.js';test_path='scripts/check-proofgraph-input.mjs'
js=(base/'sources'/js_path).read_text();test=(base/'sources'/test_path).read_text()
old="  const names = new Set();\n"
new="""  const conceptNames = new Set((isArr(report.concepts) ? report.concepts : [])
    .filter((c) => c && isStr(c.id)).map((c) => c.id));
  const requirementIds = new Set(plan.requirements.filter((r) => r && isStr(r.id)).map((r) => r.id));
  const names = new Set();
"""
assert js.count(old)==1;patched=js.replace(old,new)
old="    list(`${n.name}'s axioms`, n.axioms);\n"
new="""    list(`${n.name}'s axioms`, n.axioms);
    // The plan retains explicit placement even for goals and modules outside the population.
    // Validate it before the model uses it as a fallback for a node with no named claim.
    const placed = n.placement;
    if (placed !== null) {
      if (!placed || typeof placed !== 'object' || isArr(placed)) {
        problems.push(`${n.name}'s placement is missing or is not an object or null`);
      } else {
        if (!isStr(placed.concept) || !conceptNames.has(placed.concept))
          problems.push(`${n.name}'s placement names unknown concept ${placed.concept}`);
        if (placed.requirement !== null && (!isStr(placed.requirement) || !requirementIds.has(placed.requirement)))
          problems.push(`${n.name}'s placement names unknown requirement ${placed.requirement}`);
      }
    }
"""
assert patched.count(old)==1;patched=patched.replace(old,new)
old="const conceptIds = (report.concepts || []).map((c) => c.id);"
assert patched.count(old)==1;patched=patched.replace(old,'// pg-model:begin\n'+old)
old="concept: (claims[0] && claims[0].concept) || placement[n.name] || null,"
new="concept: (claims[0] && claims[0].concept) || (n.placement && n.placement.concept) || placement[n.name] || null,"
assert patched.count(old)==1;patched=patched.replace(old,new)
old="// ---------------------------------------------------------------- the controls"
assert patched.count(old)==1;patched=patched.replace(old,'// pg-model:end\n\n'+old)
addition="""
// The model must retain a plan node's explicit concept when no named claim or population
// entry supplies it. Goals and tagged theorems outside the concept-named modules use this path.
const modelBegin = source.indexOf('// pg-model:begin');
const modelEnd = source.indexOf('// pg-model:end');
if (modelBegin < 0 || modelEnd < modelBegin) fail('the view has no pg-model block');
const model = new Function('report', 'areaRows', 'short',
  `const plan = report.plan;\\n${source.slice(modelBegin, modelEnd)}\\nreturn { nodes, reqs };`);
const makeModel = (r) => model(r, [], (n) => n.split('.').pop());
const claimFor = (r, name) => (r.claims || []).find((c) => {
  const s = c.status || {};
  const w = s.witness || s.goal || (s.counterexample && s.counterexample.witness);
  return w && w.name === name;
});
const explicit = report.plan.nodes.filter((n) => n.placement && !claimFor(report, n.name));
if (!explicit.length) fail('the report has no explicit non-claim placement to check');
const drawn = makeModel(report);
for (const n of explicit) if (drawn.nodes.get(n.name).concept !== n.placement.concept)
  fail(`${n.name}: the model lost the plan's concept ${n.placement.concept}`);
const sample = explicit.find((n) => n.kind === 'goal') || explicit[0];
const cleanSample = () => {
  const r = copy();
  r.claims = r.claims.filter((c) => c !== claimFor(r, sample.name));
  r.placement.declarations = r.placement.declarations.filter((n) => n.name !== sample.name);
  return r;
};
const atSample = (r) => r.plan.nodes.find((n) => n.name === sample.name);
const concept = (r) => makeModel(r).nodes.get(sample.name).concept;
const tagOnly = cleanSample();
if (concept(tagOnly) !== sample.placement.concept) fail('the explicit placement alone was lost');
const inheritedOnly = cleanSample();
atSample(inheritedOnly).placement = null;
inheritedOnly.placement.declarations.push({ name: sample.name, concept: sample.placement.concept });
if (concept(inheritedOnly) !== sample.placement.concept) fail('the population fallback was lost');
const unplaced = cleanSample();
atSample(unplaced).placement = null;
if (concept(unplaced) !== null) fail('a node with no placement acquired a concept');
const claimed = cleanSample();
const otherConcept = report.concepts.find((c) => c.id !== sample.placement.concept).id;
claimed.claims.unshift({ concept: otherConcept, status: { witness: { name: sample.name } } });
if (concept(claimed) !== otherConcept) fail('the existing named-claim precedence changed');
const placementCases = [
  ['missing placement', (r) => { delete atSample(r).placement; }, 'placement is missing'],
  ['wrong placement shape', (r) => { atSample(r).placement = []; }, 'placement is missing'],
  ['unknown placement concept', (r) => { atSample(r).placement.concept = 'Unknown.concept'; }, 'Unknown.concept'],
  ['unknown placement requirement', (r) => { atSample(r).placement.requirement = 'Unknown.requirement'; }, 'Unknown.requirement'],
];
for (const [label, mutate, expected] of placementCases) {
  const broken = copy(); mutate(broken);
  if (!validatePlan(broken).some((p) => p.includes(expected))) fail(`${label}: expected ${expected}`);
}
console.log(`PASS check-proofgraph-placement: ${explicit.length} explicit non-claim placements retained; 4 precedence/fallback controls; ${placementCases.length} malformed placements refused`);
"""
patched_test=test+'\n'+addition
for path,text in [(js_path,patched),(test_path,patched_test)]:
 p=base/'candidate'/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
patch=''.join(difflib.unified_diff(js.splitlines(True),patched.splitlines(True),fromfile='a/'+js_path,tofile='b/'+js_path))+'\n'+''.join(difflib.unified_diff(test.splitlines(True),patched_test.splitlines(True),fromfile='a/'+test_path,tofile='b/'+test_path))
(base/'placement.patch').write_text(patch)
print('Scratch candidate written; repository untouched.')
