from pathlib import Path
import json,re,difflib,hashlib
root=Path('/Users/pooks/Dev/lean4-effect4-slice6');out=Path('/private/tmp/row39-series')
changes={}
p='docs/ARCHITECTURE.md';s=(root/p).read_text()
a='The schema authoring boundary sits above Program and Schema. `Schema/Image` connects\nconcrete Lean carriers to admitted program values; its proofs are `Laws/Schema/Image`.\n(`Schema/Transform` and `Schema/Endpoint`, the second authoring plane, were deleted on\n2026-09-18 under `docs/research/2026-09-17-ontology-and-do-now-probe.md` §3.)'
b='The retained Schema boundary contains the raw carriers and authoring constructors,\n`Bridge` for the program type arrow, `Codec` for type-directed JSON, and `OfShape`\nfor the Store shape arrow. Row 39 retires the separate field-admission judgment,\nprogram image, annotated-field generator and recursive annotation traversal.\nPure `Store/Domain/Shape` imports no Schema module; `Store/Domain/Canonical` owns\n`Canonical.document` through `Schema/OfShape`, and Domain/Node/Genesis retain\nschema-node and address construction. (`Schema/Transform` and `Schema/Endpoint`,\nthe second authoring plane, were deleted on 2026-09-18 under the ontology note §3.)'
assert a in s;s=s.replace(a,b).replace('text-producing generators such as `Codegen.Schema.generate?`','text-producing functions such as `Codegen.Schema.documentSource`');changes[p]=s
p='docs/GENERATED.md';s=(root/p).read_text()
s=s.replace('The rest of the Schema slice runs on its inputs as\n`make check-schema-pins` and `check-schema-host`.','The retained Schema checks run on their inputs as\n`make check-schema-pins` and `check-schema-ts`. Row 39 retires the annotation and\neffectful-field harnesses and their `check-schema-host` gate; the pinned\n`harness/schema-host` installation remains the host used by `schema-ts`.');changes[p]=s
p='tools/Tools/ArchitectureRoles.lean';s=(root/p).read_text()
a='the persisted Schema data plane; `Codec` is the type-directed JSON boundary; `Image` and `Bridge` the arrows in and out'
b='the persisted Schema data plane; `Codec` is the type-directed JSON boundary; `Bridge` and `OfShape` are the type and shape arrows'
assert a in s;s=s.replace(a,b);changes[p]=s
patch=[];inventory=[]
for p,new in changes.items():
 old=(root/p).read_text()
 patch.append('diff --git a/'+p+' b/'+p+'\n')
 patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
 inventory.append({'path':p,'old_sha256':hashlib.sha256(old.encode()).hexdigest(),'new_sha256':hashlib.sha256(new.encode()).hexdigest(),'excluded_from_code_series':True})
 dest=out/'coordinator-prose/rendered'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(new)
(out/'coordinator-prose/proposed.patch').write_text(''.join(patch))
(out/'coordinator-prose/inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
# Existing producer imports: historical dependency evidence, not a predicted output diff.
graph={}
for folder in ['src','tools','Test']:
 for f in (root/folder).rglob('*.lean'):
  if '.lake' in f.parts:continue
  p=str(f.relative_to(root));name=p[4:] if folder=='src' else p[6:] if folder=='tools' else p
  graph[name[:-5].replace('/','.')]=re.findall(r'^import ([A-Za-z0-9_.]+)',f.read_text(),re.M)
def reach(roots):
 seen=set();stack=list(roots)
 while stack:
  m=stack.pop()
  if m in seen:continue
  seen.add(m);stack.extend(graph.get(m,[]))
 return seen
deleted={'Effect4.Schema.EffectfulField','Effect4.Codegen.EffectfulField','Effect4.Schema.Check','Effect4.Schema.Accepts','Effect4.Schema.Image','Effect4.Laws.Schema.Image'}
manifest=json.loads((root/'tools/Effect4Gen/manifest.json').read_text())
rows=[]
for g in manifest['groups']:
 imps=g.get('Imports','').split(',')
 if hit:=sorted(reach(imps)&deleted):rows.append({'group':g['Name'],'imports':imps,'deleted_modules_in_old_import_closure':hit})
roots=json.loads((root/'ocaml/gen/roots.json').read_text())
lcnf=[]
for a in roots['artefacts']:
 imps=a.get('import',[])
 lcnf.append({'out':a['out'],'explicit_imports':imps,'deleted_modules_in_explicit_old_import_closure':sorted(reach(imps)&deleted),'declared_deleted_schema_roots': [x for x in a['roots'] if x.startswith(('Effect4.Schema.ProgramImage','Effect4.Schema.EffectfulField','Effect4.Codegen.Schema.generate','Effect4.Codegen.EffectfulField'))]})
others=[]
for mod in ['OCaml5.Tools.EffGen','OCaml5.Tools.EffWire','OCaml5.Tools.CasGoldens']:
 others.append({'module':mod,'deleted_modules_in_old_import_closure':sorted(reach([mod])&deleted)})
(out/'generator-input-inventory.json').write_text(json.dumps({'derived_groups':rows,'lcnf_explicit_imports':lcnf,'other_producers':others,'manifest_or_guard_patch_needed_for_same_names_topology':False,'actual_producer_inputs_edited':['harness/schema-generation/EmitFixture.lean','harness/schema-generation/EmitCoverageFixture.lean'],'notes':['SchemaFold is retained; Codegen.Schema imports it explicitly in slice 3.','Schema/Pin generated guard sources need no edits because moved declaration names remain identical.','Canonical imports OfShape explicitly, preserving Schema manifest visibility through Derived.Json.','ArchitectureRoles prose is separate coordinator-owned proposal; architecture report is not generated here.']},indent=2)+'\n')
print(json.dumps({'coordinator_prose_paths':len(changes),'derived_groups_with_deleted_imports':[r['group'] for r in rows]}))
