#!/usr/bin/env python3
"""Exercise validator failures through in-memory overlays only; never edits repo."""
from pathlib import Path
import importlib.util
import json

root=Path('/Users/pooks/Dev/lean4-effect4-slice6')
bundle=Path('/private/tmp/row39-series')
spec=importlib.util.spec_from_file_location('row39_validate',bundle/'final-validator/validate.py')
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
base=v.validate(root,bundle)
assert base['ok'],base['failures']
results=[{'control':'live_worktree_positive','ok':base['ok'],'head':base['head']}]

def expect(name,overrides,failed):
    result=v.validate(root,bundle,overrides)
    assert not result['ok'],name
    assert set(failed)<=set(result['failures']),(name,result['failures'])
    results.append({'control':name,'ok':True,'expected_failed_checks':failed,'observed_failed_checks':result['failures'],
                    'mutation':'in-memory only'})

artifact='ocaml/engine/cas/goldens/g1-censusEntry.hex'
expect('pinned_hex_byte_change',{artifact:(root/artifact).read_bytes()+b'0'},['prechange_artifact_bytes'])
source='src/Effect4/Schema/Annotations.lean'
expect('unexpected_final_source_change',{source:(root/source).read_bytes()+b'\n'},['final_source_hashes'])
archive=(root/v.ARCHIVE).read_text()
row=next(x['original_row'] for x in json.loads((bundle/'register-closure/original-rows.json').read_text()) if x['id']=='E4-SCHEMA-CE-049')
expect('retired_row_missing',{v.ARCHIVE:archive.replace(row+'\n','',1).encode()},['retired_registered_witnesses'])
expect('duplicate_retired_id',{v.ARCHIVE:(archive+'\n'+row+'\n').encode()},['retired_registered_witnesses','no_new_duplicate_id_multiplicity'])
carrier='src/Effect4/Store/Carrier/Digest.lean'
expect('stale_import_into_pure_shape_closure',{carrier:b'import Effect4.Schema.Check\n'+(root/carrier).read_bytes()},
       ['no_imports_of_deleted_modules','pure_shape_schema_free_closure'])
mask_test='''/- import Effect4.Schema.Check
 /- nested import Wrong -/
-/
-- import Effect4.Schema.Check
public import Effect4.Store.Domain.Shape
private def text := "ignored\nimport Effect4.Schema.Check\n"
private def raw := r##""a"\nimport Effect4.Schema.Check\n"##
import Effect4.Data.JsonNumber Effect4.Store.Carrier.Kind
'''
assert [name for name,_ in v.imports(mask_test)]==['Effect4.Store.Domain.Shape','Effect4.Data.JsonNumber','Effect4.Store.Carrier.Kind']
results.append({'control':'comments_strings_and_multimodule_imports','ok':True})
print(json.dumps({'ok':True,'controls':results,'repository_written':False,'compiler_or_generator_run':False},indent=2))
