#!/usr/bin/env python3
"""Reproduce lexical leads with explicit file classes; no source edits."""
from pathlib import Path
import subprocess,re,json,csv
ROOT=Path('/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4')
OUT=Path(__file__).resolve().parent
files=[p for p in subprocess.check_output(['git','ls-files','ocaml/*.ml','ocaml/**/*.ml','ocaml/*.mli','ocaml/**/*.mli'],cwd=ROOT,text=True).splitlines() if 'tools/typed_lint/test/' not in p and 'GENERATED' not in (ROOT/p).read_text()]
def category(p):
 if p.endswith('.mli'):return 'interface'
 if '/test/' in p or Path(p).name.startswith(('test_','bench_','probe_')) or '/bench/' in p or p.endswith('/join_escape.ml'):return 'test-bench'
 if '/tools/' in p:return 'tool-or-template'
 if '/bin/' in p:return 'driver'
 return 'library'
patterns={x:re.compile(r'\b'+re.escape(x)+r'\b') for x in ['failwith','invalid_arg','Option.get','List.hd','List.nth','mutable','compare','Mutex','Atomic','Domain.spawn']}
patterns['ignore (']=re.compile(r'ignore \(')
rows=[]
for p in files:
 for n,line in enumerate((ROOT/p).read_text().splitlines(),1):
  for pat,rx in patterns.items():
   if rx.search(line):rows.append(dict(path=p,line=n,category=category(p),pattern=pat,text=line))
summary={pat:{cat:sum(r['pattern']==pat and r['category']==cat for r in rows) for cat in sorted(set(category(p) for p in files))} for pat in patterns}
libs=[p for p in files if category(p)=='library']
missing=[p for p in libs if not (ROOT/Path(p).with_suffix('.mli')).exists()]
constants={}
for p in libs:
 literals=re.findall(r'(?<![\w])[0-9]+(?![\w])',(ROOT/p).read_text())
 constants[p]=sum(int(x)>2 for x in literals)
manifest={}
for p in sorted((ROOT/'ocaml/gen').glob('closure-*.tsv')):
 manifest[p.name]=len(list(csv.DictReader(p.read_text().splitlines()[1:],delimiter='\t')))
res=dict(hand_files=len(files),classes={c:sum(category(p)==c for p in files) for c in sorted(set(category(p) for p in files))},summary=summary,missing_interfaces=missing,manifest_rows=manifest,numeric_literal_leads=sorted(constants.items(),key=lambda t:-t[1]),files=files,libraries=libs,rows=rows)
(OUT/'inventory.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({k:v for k,v in res.items() if k not in ['rows','files','libraries','numeric_literal_leads']},indent=2))
