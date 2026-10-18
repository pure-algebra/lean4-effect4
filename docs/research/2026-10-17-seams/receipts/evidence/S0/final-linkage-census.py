from pathlib import Path
import re
r=Path('/Users/pooks/.codex/worktrees/seams/lean4-effect4')
o=Path('/private/tmp/seams-s0-linkage-overlay')
text=(r/'ocaml/engine/e4_engine_intf.ml').read_text().split('module type INSTANCE = sig',1)[1].split('module type ENGINE = sig',1)[0]
required=set(re.findall(r'\bval\s+([a-z_][a-zA-Z0-9_\']*)\s*:',text))
for adapter,public,wrapper in [('engine/e4_instance.ml','engine/api_engine.mli',{'name','carriers'}),('engine/test/api_gen_inst.ml','gen/api_gen.mli',set())]:
 definitions=set(re.findall(r'^\s*let(?:\s+rec)?\s+([a-z_][a-zA-Z0-9_\']*)\b',(o/adapter).read_text(),re.M))
 exported=set(re.findall(r'\bval\s+([a-z_][a-zA-Z0-9_\']*)\s*:',(o/public).read_text()))
 missing=required-definitions-exported-wrapper
 print(adapter, 'required',len(required),'missing',sorted(missing))
 print('inherited',sorted(required-definitions-wrapper))
 assert not missing
print('PASS complete instance value inventory against the fresh corrected native interfaces')
