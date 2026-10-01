from pathlib import Path
import json,re,hashlib
R=Path('/Users/pooks/Dev/lean4-effect4-slice6')
S=Path('/private/tmp/row39-series')
P=S/'projected'
oldshape=(R/'src/Effect4/Store/Domain/Shape.lean').read_text()
newshape=(P/'src/Effect4/Store/Domain/Shape.lean').read_text()
ofshape=(P/'src/Effect4/Schema/OfShape.lean').read_text()
oldann=(R/'src/Effect4/Schema/Annotations.lean').read_text()
newann=(P/'src/Effect4/Schema/Annotations.lean').read_text()
def section(text,start,end):
    return text[text.index(start):text.index(end,text.index(start))].strip()
checks={
'identifierKey_exact':section(oldshape,'def identifierKey :','theorem identifierKey_lawful')==section(ofshape,'def identifierKey :','theorem identifierKey_lawful'),
'refKey_exact':section(oldshape,'def refKey :','theorem refKey_lawful')==section(ofshape,'def refKey :','theorem refKey_lawful'),
'rendering_block_exact':section(oldshape,'/-! ## The spec: `ShapeDoc.document` -/','/-! ## The printer: `ShapeDoc.print` -/')==section(ofshape,'/-! ## The spec: `ShapeDoc.document` -/','/-! Existing finite rendering receipts'),
'nodeAnnotations_definition_exact':section(oldann,'def nodeAnnotations :','theorem nodeAnnotations_reference')==section(newann,'def nodeAnnotations :','theorem nodeAnnotations_lawful'),
'key_laws_exact':section(oldann,'structure Lawful (key : AnnotationKey A)','/-- Encode one typed value')==section(newann,'structure Lawful (key : AnnotationKey A)','/-- Encode one typed value'),
'key_carrier_exact':section(oldann,'structure AnnotationKey','namespace AnnotationKey')==section(newann,'structure AnnotationKey','namespace AnnotationKey'),
'entry_singleton_append_exact':section(oldann,'def entry (key : AnnotationKey A)','/-- Decode an entry')==section(newann,'def entry (key : AnnotationKey A)','end AnnotationKey'),
}
# Remove only the moved renderer/key region, opening imports/comment adjustments,
# and exact four rendering guard lines; remaining computational tail must match.
moved=[l for l in ofshape.splitlines() if l.startswith('#guard')]
checks['four_guards_exact_and_removed']=len(moved)==4 and all(l in oldshape and l not in newshape for l in moved)
old_printer_tail=section(oldshape,'/-! ## The printer: `ShapeDoc.print` -/','/-! ## Receipts')
new_printer_tail=section(newshape,'/-! ## The printer: `ShapeDoc.print` -/','/-! ## Receipts')
checks['pure_printer_tail_exact_except_four_moved_guards']='\n'.join(l for l in old_printer_tail.splitlines() if l not in moved).strip()==new_printer_tail.strip()
# Build our own effective local import graph from the full source tree + overlay.
texts={str(p.relative_to(R)):p.read_text() for p in (R/'src').rglob('*.lean')}
series=json.loads((S/'series.json').read_text())
for stage in series['stages']:
    for change in stage['changes']:
        rel=change['path']
        if not rel.startswith('src/') or not rel.endswith('.lean'): continue
        if change['action']=='delete': texts.pop(rel,None)
        else: texts[rel]=(S/stage['stage']/'rendered'/rel).read_text()
mods={rel.removeprefix('src/').removesuffix('.lean').replace('/','.'):text for rel,text in texts.items()}
graph={m:re.findall(r'^import\s+([A-Za-z0-9_.]+)',t,re.M) for m,t in mods.items()}
def closure(m):
    visited=set(); pending=[m]
    while pending:
        x=pending.pop()
        if x in visited:continue
        visited.add(x); pending.extend(graph.get(x,[]))
    return visited
shapeclosure=sorted(closure('Effect4.Store.Domain.Shape'))
checks['shape_schema_free']=not any(m.startswith('Effect4.Schema') for m in shapeclosure)
checks['ofshape_reachable_from_effect4']='Effect4.Schema.OfShape' in closure('Effect4')
checks['ofshape_avoids_canonical_cycle']='Effect4.Store.Domain.Canonical' not in closure('Effect4.Schema.OfShape')
checks['printer_imports_fold_directly']='Effect4.Schema.Fold' in graph['Effect4.Codegen.Schema']
checks['annotations_no_fold_import']='Effect4.Schema.Fold' not in graph['Effect4.Schema.Annotations']
checks['canonical_explicit_ofshape']='Effect4.Schema.OfShape' in graph['Effect4.Store.Domain.Canonical']
# Preserve raw Document result and the complete Node/Genesis implementation.
checks['document_raw_result']='def ShapeDoc.document (doc : ShapeDoc) : Document :=' in ofshape
checks['node_genesis_untouched']=all(not any(c['path']==f'src/Effect4/Store/Domain/{n}.lean' for s in series['stages'] for c in s['changes']) for n in ['Node','Genesis'])
out={'checks':checks,'pure_shape_closure':shapeclosure,'reviewed_files':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [S/'03-annotations/source.patch',S/'04-of-shape/source.patch']},'scope':'Static source/import comparison only; no Lean or generated output execution'}
Path('/private/tmp/row39-independent-review/checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(checks,indent=2))
assert all(v is True or v is None for v in checks.values())
