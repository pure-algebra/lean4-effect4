#!/usr/bin/env python3
"""Copy the four modules to a fresh namespace with source mapping; no Lean or repo writes."""
import argparse, csv, hashlib, json, re
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--input',required=True,type=Path)
ap.add_argument('--out',required=True,type=Path)
ap.add_argument('--name',default='PartOne')
ap.add_argument('--namespace',default='Research.Slice6.H2PartOne')
a=ap.parse_args(); source=a.input.resolve(); out=a.out.resolve()
if not out.is_relative_to(Path('/private/tmp')): raise RuntimeError('output must be under /private/tmp')
if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',a.name): raise RuntimeError('invalid probe name')
prefix=Path('src/Effect4/Laws/Program/Typed')
if (source/prefix/'Scheduler.lean').exists():
    raise RuntimeError('four-module harness is incomplete after H1 Scheduler lands; inventory it first')
ns0='Effect4.Program.Typed'; ns=a.namespace
lines=['import Effect4.Laws.Program.Typed.Assembly','',
'/-! Research-only concatenation. Definitions, signatures and proof bodies are copied from the',
'named candidate. Imports and post-namespace proofgraph commands are omitted; see the map.',
'This checks copied declarations, not production module integration or obligation ceilings. -/','',
'open Effect4.Program.Typed','',f'namespace {ns}',
'abbrev World := Effect4.Program.Typed.World',f'end {ns}','']
mapping={'probe':a.name,'namespace':ns,'sections':[],'declarations':[],'line_map':[]}
for module in ('Admission','Residual','Stack','Assembly'):
    path=source/prefix/(module+'.lean'); text=path.read_text(); original=text.splitlines()
    if 'import Effect4.Laws.Program.Typed.Scheduler' in text:
        raise RuntimeError('Assembly requires H1 Scheduler; four-module harness cannot cover it')
    lines.extend([f'/-! Source block: {module}.lean ({a.name}). -/',''])
    section={'module':module,'input_path':str(path),'input_sha256':hashlib.sha256(text.encode()).hexdigest(),
             'harness_start':len(lines)+1,'imports_omitted':[]}
    namespaces=[]; local_decls=[]; finished=False
    for i,s in enumerate(original,1):
        if s.startswith('import '): section['imports_omitted'].append(s); continue
        if finished: continue
        transformed=s.replace(ns0,ns)
        lines.append(transformed); hline=len(lines)
        mapping['line_map'].append({'harness_line':hline,'module':module,'source_line':i,'input_path':str(path)})
        if s.startswith('namespace '): namespaces.append(s[len('namespace '):].strip())
        elif s.startswith('end ') and namespaces: namespaces.pop()
        d=re.match(r'^(?:private |protected )?(def|theorem|inductive|structure|abbrev) ([^\s(:]+)',s)
        if d:
            if local_decls:
                local_decls[-1].update(source_end=i-1,harness_end=hline-1)
            kind,name=d.groups(); full='.'.join(namespaces+[name])
            local_decls.append({'kind':kind,'original_declaration':full,
              'harness_declaration':full.replace(ns0,ns),'module':module,
              'source_module':'Effect4.Laws.Program.Typed.'+module,'input_path':str(path),
              'source_start':i,'harness_start':hline})
        if s == 'end '+ns0:
            finished=True
            section['post_namespace_lines_omitted']=([i+1,len(original)] if i<len(original) else None)
            if local_decls: local_decls[-1].update(source_end=i-1,harness_end=hline-1)
    if not finished: raise RuntimeError('missing namespace end in '+str(path))
    section['harness_end']=len(lines); mapping['sections'].append(section)
    mapping['declarations'].extend(local_decls); lines.append('')
result='\n'.join(lines)+'\n'; mapping['harness_sha256']=hashlib.sha256(result.encode()).hexdigest()
out.mkdir(parents=True,exist_ok=True)
(out/(a.name+'.lean')).write_text(result)
(out/(a.name+'.map.json')).write_text(json.dumps(mapping,indent=2)+'\n')
with (out/(a.name+'.theorems.csv')).open('w',newline='') as f:
    writer=csv.DictWriter(f,fieldnames=('module','original_declaration','harness_declaration','source_start','harness_start'))
    writer.writeheader()
    writer.writerows({k:d[k] for k in writer.fieldnames} for d in mapping['declarations'] if d['kind']=='theorem')
print(json.dumps({'harness':str(out/(a.name+'.lean')),'source_modules':4,
    'mapped_declarations':len(mapping['declarations']),'lines':len(lines)},indent=2))
