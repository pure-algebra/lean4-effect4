from pathlib import Path
import difflib, hashlib, json, re, subprocess
repo=Path('/Users/pooks/Dev/lean4-effect4-slice6')
out=Path('/private/tmp/row39-series')
base=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
original={}; projected={}; stages=[]; modes={}
expected=json.loads((out/'inputs/expected-source-hashes.json').read_text())
for p,wanted in expected.items():
    got=hashlib.sha256((repo/p).read_bytes()).hexdigest()
    assert got==wanted,('input snapshot is stale; regenerate candidate instead of overwriting',p,wanted,got)
def sha(text):return None if text is None else hashlib.sha256(text.encode()).hexdigest()
def read(p):
    if p in projected:
        assert projected[p] is not None, ('deleted',p)
        return projected[p]
    s=(repo/p).read_text(); original[p]=s; projected[p]=s
    rec=subprocess.check_output(['git','ls-files','-s','--',p],cwd=repo,text=True).split()
    assert rec,('not tracked',p)
    modes[p]=rec[0]
    return s
def rep(s,a,b):
    assert s.count(a)==1,('expected one',a,s.count(a))
    return s.replace(a,b)
def drop(s,a,b):
    start=s.index(a); end=s.index(b,start)
    return s[:start]+s[end:]
def edit(p,s):
    if p not in projected:
        assert not (repo/p).exists(),('new exists',p)
        original[p]=None; projected[p]=None; modes[p]='100644'
    projected[p]=s
def delete(p):read(p); projected[p]=None
def remove_imports(p,modules):
    s=read(p)
    for m in modules:s=rep(s,'import '+m+'\n','')
    edit(p,s)
def files(p):return subprocess.check_output(['git','ls-files',p],cwd=repo,text=True).splitlines()
def begin(name):
    stages.append({'name':name,'before':dict(projected),'files':None})
def finish():
    stage=stages[-1]; before=stage['before']; changed={}
    for p,new in projected.items():
        old=before.get(p,original[p])
        if old!=new:changed[p]=(old,new)
    stage['files']=changed

# 01 -- remove EffectfulField and only its half of the shared host gate.
begin('01-effectful-field')
deleted=['src/Effect4/Schema/EffectfulField.lean','src/Effect4/Codegen/EffectfulField.lean',
'Test/Schema/EffectfulFieldContract.lean','Test/Schema/EffectfulFieldPropertiesContract.lean',
'Test/Counterexamples/Schema/EffectfulField.lean','Test/Counterexamples/Schema/EffectfulFieldProperties.lean',
'Test/Codegen/EffectfulFieldContract.lean','Test/Counterexamples/Codegen/EffectfulField.lean',
*files('harness/schema-effectful-field'),'scripts/check-schema-effectful-field.sh']
for p in deleted:delete(p)
remove_imports('src/Effect4.lean',['Effect4.Schema.EffectfulField','Effect4.Codegen.EffectfulField'])
s=read('src/Effect4.lean').replace('-- checker, the authoring face, and the value, getter, transformation, codec,','-- checker, the authoring face, and the value, transformation, codec,').replace('-- The Effect TypeScript target: the Schema and annotated-field generators.','-- The Effect TypeScript target: the Schema generator.')
edit('src/Effect4.lean',s)
remove_imports('Test/All.lean',[p[:-5].replace('/','.') for p in deleted if p.startswith('Test/') and p.endswith('.lean')])
p='Test/Audit/AxiomGate.lean';s=read(p)
s=rep(s,"semantic/test ceiling, and this list is what says which is which. The field\nreceipt's statement itself uses the renderer and `String.contains`; it is not a\nsemantic admission theorem. `docs/research/TYPESCRIPT-TARGET-DAG.md` records this\nimplementation boundary.","semantic/test ceiling, and this list is what says which is which.\n`docs/research/TYPESCRIPT-TARGET-DAG.md` records this implementation boundary.")
s=rep(s,'  -- The raw Schema and annotated-field generators: source text out.','  -- The raw Schema generator: source text out.')
for name in ['source?','generate?','source_contains_directional_rows']:s=rep(s,'  , ``Effect4.Codegen.EffectfulField.'+name+'\n','')
s=rep(s,'  [ (`Effect4.Codegen.EffectfulField,\n      `Effect4.Codegen.EffectfulField.directionalRowsPresent)\n','')
s=rep(s,'  , (`Effect4.Program.Config, `Effect4.Program.Config.ce006Late)\n','  [ (`Effect4.Program.Config, `Effect4.Program.Config.ce006Late)\n')
edit(p,s)
p='Makefile';s=read(p)
s=rep(s,'$(shell find harness/schema-annotations harness/schema-effectful-field -type f -not -path \'*/node_modules/*\') scripts/check-schema-annotations.sh scripts/check-schema-effectful-field.sh','$(shell find harness/schema-annotations -type f -not -path \'*/node_modules/*\') scripts/check-schema-annotations.sh')
s=rep(s,'\tbash scripts/check-schema-effectful-field.sh\n','');edit(p,s)
p='.github/workflows/lean_action_ci.yml';s=read(p)
s=rep(s,'The Schema slice on the pinned host (generation, the tag and field pins, the two harnesses)','The Schema slice on the pinned host (generation, tag pins, and annotation fields)');edit(p,s)
finish()

# 02 -- remove Check/Accepts/Image and their legacy convenience admission.
begin('02-check-accepts-image')
deleted=['src/Effect4/Schema/Check.lean','src/Effect4/Schema/Accepts.lean','src/Effect4/Schema/Image.lean','src/Effect4/Laws/Schema/Image.lean',
*[p for p in files('Test/Counterexamples/Schema') if p.endswith('.lean') and projected.get(p,'present') is not None],
*files('harness/schema-annotations'),'scripts/check-schema-annotations.sh']
for p in deleted:delete(p)
remove_imports('src/Effect4.lean',['Effect4.Schema.Check','Effect4.Schema.Accepts'])
s=read('src/Effect4.lean')
s=rep(s,'-- The Schema data plane: the persisted carrier, the annotation data plane, the\n-- checker, the authoring face, and the value, transformation, codec,\n-- registry and foreign rows.','-- The Schema data plane: the persisted carriers, annotations and raw authoring face.')
s=rep(s,'-- Structural acceptance of persisted Schema documents.\n','');edit('src/Effect4.lean',s)
remove_imports('src/Effect4/Laws.lean',['Effect4.Laws.Schema.Image'])
remove_imports('Test/All.lean',[p[:-5].replace('/','.') for p in deleted if p.startswith('Test/') and p.endswith('.lean')])
p='src/Effect4/Schema/Authoring.lean';s=read(p)
s=rep(s,'import Effect4.Schema.Check','import Effect4.Schema.Document')
s=drop(s,'universe u v\n','/-! ## Registered, persisted check descriptions -/')
edit(p,s)
p='Test/Schema/AuthoringContract.lean';s=read(p)
s=drop(s,'#check Effect4.Schema.Predicate.decide','private def nameSchema')
s=drop(s,'private def even (value : Nat)', '#guard nameSchema')
edit(p,s)
p='Test/Schema/PayloadContract.lean';s=read(p)
s=rep(s,'import Effect4.Schema.Check\n','')
s=drop(s,'/-! ## D7 — persisted/decode-side field admission', '/-! ## Enforcement by absence')
s=rep(s,'while D4-D7 must not leak upward','while D4-D6 must not leak upward')
start=s.index('\n  , "/-- error: Unknown -/"\n  , "#guard_msgs(error, substring := true) in #check (@Effect4.Annotations.FieldAdmissible)"')
end=s.index(' ]',start)+2
s=s[:start]+' ]'+s[end:]
s=rep(s,'Breaker-owned red battery for the Schema representation PAYLOAD carrier — the\nrecursive first-order tree that hangs off the frozen 22-tag census. The\nimplementation phase must not edit this file. It is red until the payload\ndeclarations exist, and every pre-implementation failure must be a\n`lean.unknownIdentifier` diagnostic naming a frozen declaration.\n\nTargets `SC-REP-01` (declaration half), `SC-REP-04` (clause half), and the\npayload half of `SC-REP-03` (structural equality). It makes no denotation,','Retained receipts for the Schema representation PAYLOAD carrier — the\nrecursive first-order tree that hangs off the frozen 22-tag census. Row 39\nretires the former field-admission judgment and its D7 checks.\n\nTargets `SC-REP-01` (declaration half) and the payload half of `SC-REP-03`\n(structural equality). It makes no denotation,')
edit(p,s)
p='src/Effect4/Schema/Payload.lean';s=read(p)
s=rep(s,'constraints are checked later by `Effect4.Schema.Check`; they are not hidden\ninside constructors here.','constraints belong to the persisted host decoding boundary; they are not\nhidden inside constructors here. Row 39 retires the separate Lean field-admission\njudgment while retaining these raw carriers.')
edit(p,s)
p='src/Effect4/Schema/Document.lean';s=read(p)
s=rep(s,'non-empty-root admission clause of `src/Effect4/Schema/Check.lean`, and\n`MultiDocument.fieldAdmissible_two_roots` records that this witness is itself\nfield-admissible.','non-empty-root constraint of the persisted host document codec. This theorem\nconcerns the raw container embedding alone.')
edit(p,s)
# Apply only the transformations of the previously prepared convenience patch,
# against the current projected state so slice 1's gate cleanup is retained.
p='src/Effect4/Codegen/Schema.lean';read(p)
edit(p,(out/'inputs/convenience/src/Effect4/Codegen/Schema.lean').read_text())
for p in ['Test/Codegen/SchemaGenerationContract.lean','Test/Codegen/SchemaGenerationCoverage.lean','harness/schema-generation/EmitFixture.lean','harness/schema-generation/EmitCoverageFixture.lean','src/Effect4/Codegen/Target.lean']:
    read(p);edit(p,((out/'inputs/convenience')/p).read_text())
p='Test/Audit/AxiomGate.lean';s=read(p)
s=rep(s,'  , ``Effect4.Codegen.Schema.source?\n  , ``Effect4.Codegen.Schema.generate?\n','');edit(p,s)
p='src/Effect4/Api.lean';s=read(p)
s=rep(s,'import Effect4.Schema.Image\n','')
s=drop(s,"/-- A program's boundary schema document (Decision 12 / S-4):",'/-- The program as one TypeScript expression')
s=rep(s,'/-! ## The program image -/\n\nexport Effect4.Schema (ProgramImage)\n\n','')
s=rep(s,'* The Schema half: a persisted document or representation as its `Schema.Struct({…})`\n  syntax (`schemaDocument`, `schemaRepresentation`) and the JSON payload beside it\n  (`jsonExpr`). Text generation with its module assembler is\n  `Effect4.Codegen.Schema.generate?`, admitted by exact name in the axiom gate.','* The Schema half: persisted `SchemaRepresentation` JSON syntax\n  (`schemaDocument`, `schemaRepresentation`) and the JSON payload beside it\n  (`jsonExpr`). `Codegen.Schema.moduleSyntax` assembles raw module syntax;\n  `Effect4.Codegen.Schema.documentSource` renders one raw document and is admitted\n  by exact name in the axiom gate.')
s=rep(s,'/-- A persisted Schema document as its `Schema.Struct({…})` Program. -/','/-- A persisted Schema document as raw `SchemaRepresentation` JSON syntax. -/')
s=rep(s,'/-- A persisted representation as its Schema Program. -/','/-- A persisted representation as raw `SchemaRepresentation` JSON syntax. -/')
edit(p,s)
p='Makefile';s=read(p)
s=rep(s,'(check-schema-ts, check-schema-host)','(check-schema-ts)')
s=rep(s,'host-protocol census schema-ts schema-pins schema-host tools corpus','host-protocol census schema-ts schema-pins tools corpus')
s=rep(s,'check-schema-pins check-schema-host ##','check-schema-pins ##')
s=drop(s,'$(CHK)/schema-host:', '# The one tool harness:')
s=rep(s,"schema-pins, schema-host, tools'","schema-pins, tools'")
s=rep(s,'# are a textual extraction from the vendored SchemaRepresentation.ts; the host\n# harnesses run the pinned Schema host (EFFECT4_EFFECT_NODE_MODULES, harness/schema-host).','# are a textual extraction from the vendored SchemaRepresentation.ts. The retained\n# generation gate uses the pinned host (EFFECT4_EFFECT_NODE_MODULES, harness/schema-host).')
edit(p,s)
p='.github/workflows/lean_action_ci.yml';s=read(p)
s=rep(s,'The Schema slice on the pinned host (generation, tag pins, and annotation fields)','The Schema slice on the pinned host (generation and tag pins)')
s=rep(s,'make build check-schema-ts check-schema-pins check-schema-host','make build check-schema-ts check-schema-pins');edit(p,s)
finish()

# 03 -- minimum annotation keys/local optional, no recursive annotation traversal.
begin('03-annotations')
for p in ['src/Effect4/Schema/Annotations.lean','Test/Schema/AnnotationDataPlaneContract.lean']:
    read(p)
    candidate=((out/'inputs/annotation')/p).read_text()
    if p.endswith('/Annotations.lean'):
        candidate=rep(candidate,'cases source <;> first | rfl | cases absent','cases source <;> cases absent <;> rfl')
        candidate=rep(candidate,'cases source <;> first | rfl | cases present','cases source <;> cases present <;> rfl')
    edit(p,candidate)
p='src/Effect4/Schema/Document.lean';s=read(p)
s=drop(s,'/-- Every annotation bag in the root and every stored reference entry, in','end Document')
s=drop(s,'/-- Every annotation bag in every root and stored reference entry, in','end MultiDocument')
s=rep(s,'/-! ## Structural annotation data plane\n\nThese traversals are deliberately acyclic: they visit the stored document\ncontainers and delegate each representation subtree to\n`Representation.annotationBags`.  Reference keys are never resolved, so dead\nand duplicate entries remain visible in their original order.','/-! ## Structural representation sites\n\nThese retained traversals visit only the roots and stored reference representations.\nReference keys are never resolved, so dead and duplicate entries remain visible\nin their original order. The recursive annotation traversal is retired by row 39.')
edit(p,s)
p='src/Effect4/Codegen/Schema.lean';s=read(p)
s=rep(s,'import Effect4.Schema.Authoring\n','import Effect4.Schema.Authoring\nimport Effect4.Schema.Fold\n');edit(p,s)
finish()

# 04 -- exact renderer relocation; total raw document result and bytes preserved.
begin('04-of-shape')
p='src/Effect4/Store/Domain/Shape.lean';s=read(p)
start=s.index('/-! ## The annotation keys -/');end=s.index('/-! ## The printer: `ShapeDoc.print` -/',start)
block=s[start:end]
s=s[:start]+s[end:]
guards=['#guard entryDoc.document.references.length = 1\n','#guard (entryDoc.document.representation).tag = .objects\n','#guard (render (.sum "ExportKind" [("const", 0, []), ("function", 1, [])])).tag = .union\n','#guard (render .nat).tag = .number\n']
for guard in guards:s=rep(s,guard,'')
s=rep(s,'import Effect4.Schema.Authoring\n','')
s=rep(s,'open Effect4 (Json Float64 Representation Document AnnotationKey Annotations ReferenceEntry\n  PropertySignature)','open Effect4 (Json Float64)')
header_start=s.index('/-!\n# Store.Shape');header_end=s.index('-/\n',header_start)+3
header='''/-!
# Store.Shape

Owner: the pure shape language a canonical carrier describes itself in, the checker
that says a value tree fits a shape, and the JSON printer. The downstream
`Effect4.Schema.OfShape` module owns the schema rendering arrow; this foundation
imports no Schema module. Store Domain remains above Schema.

A `ShapeDoc {root, defs}` owns the description used by `ShapeDoc.accepts` and
`ShapeDoc.print`. The schema document is derived downstream from that same data.
A `sum` names each case's wire tag, assigned by `tools/Effect4Gen/wire-tags.json`;
tags are not declaration positions, may be sparse, and are checked for repeats
by `ShapeDoc.wellTagged`.

`accepts` is structural on the value. A `named n` shape is resolved through
`defs`: `candidates` lists every binding of `n`, and a value fits when it fits
one candidate. This permits `acceptsIn_mono` and the product Canonical instance's
appended tables without a uniqueness field in the class. A definition whose
body is itself `named` is one step away and accepts nothing.

The printer uses lowercase hex and the JSON-number rule `Json.ofNat` over
`binary64OfNat`, owned by `Effect4.Arch.JsonNumber` in Data/JsonNumber. The distinct
`Shape.render : Shape → String` below supplies the structural Repr only.
-/
'''
s=s[:header_start]+header+s[header_end:]
edit(p,s)
# Proof bodies are not blindly moved with forbidden fallback/simp syntax.
block=rep(block,'''theorem identifierKey_lawful : identifierKey.Lawful := by
  constructor
  · intro value; rfl
  · intro raw value decoded
    cases raw <;> simp [identifierKey] at decoded ⊢
    exact decoded.symm
''','''theorem identifierKey_lawful : identifierKey.Lawful := by
  constructor
  · intro value; rfl
  · intro raw value decoded
    cases raw with
    | str rawValue =>
        change some rawValue = some value at decoded
        change Json.str value = Json.str rawValue
        exact congrArg Json.str (Option.some.inj decoded).symm
    | null => exact nomatch decoded
    | bool _ => exact nomatch decoded
    | number _ => exact nomatch decoded
    | arr _ => exact nomatch decoded
    | obj _ => exact nomatch decoded
''')
block=rep(block,'''theorem refKey_lawful : refKey.Lawful := by
  constructor
  · intro k
    exact Kind.ofName?_name k
  · intro raw k decoded
    cases raw <;> simp [refKey] at decoded ⊢
    exact Kind.name_ofName? decoded
''','''theorem refKey_lawful : refKey.Lawful := by
  constructor
  · intro k
    exact Kind.ofName?_name k
  · intro raw k decoded
    cases raw with
    | str value =>
        change Kind.ofName? value = some k at decoded
        change Json.str k.name = Json.str value
        exact congrArg Json.str (Kind.name_ofName? decoded)
    | null => exact nomatch decoded
    | bool _ => exact nomatch decoded
    | number _ => exact nomatch decoded
    | arr _ => exact nomatch decoded
    | obj _ => exact nomatch decoded
''')
ofshape='''import Effect4.Store.Domain.Shape
import Effect4.Schema.Authoring

/-!
# Schema.OfShape

Owner: the existing Q5 arrow from Store.Shape to persisted Schema representation,
and from ShapeDoc to its raw Document. The rendering table and reference order are
unchanged by this relocation. The raw document remains total: row 8's duplicate-key
refusal is a separate open behavior change, not a property of this arrow.

Canonical.document stays owned by Store.Domain.Canonical; schema-node and address
construction stay in Store.Domain.Node/Genesis, above Schema. They consume this one
rendering implementation. Domain schema bytes keep their version-0 behavior.
-/

set_option autoImplicit false

namespace Effect4.Store

open Effect4 (Json Float64 Representation Document AnnotationKey Annotations ReferenceEntry
  PropertySignature)

'''+block+'''/-! Existing finite rendering receipts, moved with their owner. -/

'''+''.join(guards)+'''
end Effect4.Store
'''
edit('src/Effect4/Schema/OfShape.lean',ofshape)
p='src/Effect4/Store/Domain/Canonical.lean';s=read(p)
s=rep(s,'import Effect4.Store.Domain.Shape\n','import Effect4.Store.Domain.Shape\nimport Effect4.Schema.OfShape\n')
s=rep(s,"/-- The spec of a carrier's shape. -/","/-- The raw schema document of a carrier's shape, owned here in Store Domain\nand rendered by the downstream Schema.OfShape arrow. -/")
edit(p,s)
p='src/Effect4/Codegen/Schema.lean';s=read(p)
s=rep(s,'import Effect4.Schema.Authoring\n','import Effect4.Schema.Authoring\nimport Effect4.Schema.OfShape\n');edit(p,s)
p='src/Effect4/Api.lean';s=read(p)
s=rep(s,'import Effect4.Schema.Bridge\n','import Effect4.Schema.Bridge\nimport Effect4.Schema.OfShape\n');edit(p,s)
p='Test/Schema/DialectContract.lean';s=read(p)
s=rep(s,'import Effect4.Store.Domain.Shape\n','import Effect4.Schema.OfShape\n');edit(p,s)
finish()

# Record working-source overrides separately from the named commit; never claim
# an uncommitted integration anchor was already present in that commit.
source_overrides=[]
for path,content in original.items():
    if content is None:continue
    committed=subprocess.check_output(['git','show',base+':'+path],cwd=repo,text=True)
    if committed!=content:
        source_overrides.append({'path':path,'commit_sha256':sha(committed),'working_sha256':sha(content)})
        assert path=='Test/All.lean',('unexpected uncommitted row39 input',path)
        anchor_line='import Test.Program.TypedControl\n'
        assert content==committed.replace(anchor_line,anchor_line+'import Test.Program.H2PartOne\n'),('unexpected Test.All change beyond authorized H2 anchor',path)

# Emit sequential patches and all small projected files, never the real checkout.
all_inventory=[]
for stage in stages:
    dest=out/stage['name'];dest.mkdir(parents=True,exist_ok=True)
    patch=[];inventory=[]
    for p,(old,new) in stage['files'].items():
        patch.append('diff --git a/'+p+' b/'+p+'\n')
        if old is None:patch.append('new file mode '+modes[p]+'\n')
        if new is None:patch.append('deleted file mode '+modes[p]+'\n')
        patch.extend(difflib.unified_diff([] if old is None else old.splitlines(True),[] if new is None else new.splitlines(True),fromfile='/dev/null' if old is None else 'a/'+p,tofile='/dev/null' if new is None else 'b/'+p))
        action='create' if old is None else 'delete' if new is None else 'edit'
        inventory.append({'path':p,'action':action,'old_sha256':sha(old),'new_sha256':sha(new),'mode':modes[p]})
        if new is not None:
            target=dest/'rendered'/p;target.parent.mkdir(parents=True,exist_ok=True);target.write_text(new)
    (dest/'source.patch').write_text(''.join(patch))
    meta={'base':base,'source_overrides':source_overrides,'stage':stage['name'],'applied_to_repo':False,'changes':inventory}
    (dest/'inventory.json').write_text(json.dumps(meta,indent=2)+'\n')
    all_inventory.append(meta)
(out/'series.json').write_text(json.dumps({'base':base,'source_overrides':source_overrides,'repo':str(repo),'stages':all_inventory},indent=2)+'\n')
# Projected tree contains only changed paths, plus newly created paths. No full research copy.
projection=out/'projected'
for p,s in original.items():
    if s is not None:
        d=projection/p;d.parent.mkdir(parents=True,exist_ok=True);d.write_text(s);d.chmod(int(modes[p],8)&0o777)
    elif (projection/p).exists():(projection/p).unlink()
checks=[]
for stage in stages:
    patch=out/stage['name']/'source.patch'
    result=subprocess.run(['git','apply','--check',str(patch)],cwd=projection,text=True,capture_output=True)
    checks.append({'stage':stage['name'],'check_exit':result.returncode,'stderr':result.stderr})
    assert result.returncode==0,checks[-1]
    result=subprocess.run(['git','apply',str(patch)],cwd=projection,text=True,capture_output=True)
    assert result.returncode==0,(stage['name'],result.stderr)
for p,new in projected.items():
    assert ((projection/p).read_text() if (projection/p).exists() else None)==new,p
(out/'static-patch-checks.json').write_text(json.dumps(checks,indent=2)+'\n')
(out/'base-hashes.json').write_text(json.dumps({p:{'sha256':sha(s),'mode':modes[p]} for p,s in original.items()},indent=2)+'\n')
print(json.dumps([{'stage':s['name'],'paths':len(s['files']),'deleted':sum(new is None for old,new in s['files'].values())} for s in stages]))
