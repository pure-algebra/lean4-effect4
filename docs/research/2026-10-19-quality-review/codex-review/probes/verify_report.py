from pathlib import Path
import json,re,subprocess,hashlib
R=Path(__file__).resolve().parent.parent;P=R/'probes';W=Path('/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4');M=Path('/Users/pooks/Dev/lean4-effect4')
def cmd(args,cwd):
 r=subprocess.run(args,cwd=cwd,text=True,capture_output=True);return dict(command=args,cwd=str(cwd),exit=r.returncode,stdout=r.stdout,stderr=r.stderr)
s=(R/'README.md').read_text()
a=re.findall(r'^### (A\d+\.\d+) ',s,re.M);b=re.findall(r'^### (B\d+\.\d+) ',s,re.M)
branches=json.loads((P/'backlog/branches.json').read_text());research=json.loads((P/'research-inventory.json').read_text())
links=[]
for link in re.findall(r'\]\(([^)]+)\)',s):
 if '://' not in link:
  p=R/link.split('#')[0];links.append({'link':link,'exists':p.exists()})
required=['a1.log','a1-lean.log','a1-fields.log','a1-size.json','a1-bench-before.log','a2/results.json','a2/controls.log','a2/pack-boundary.log','a2/deep-results.json','b4-json.log','b5/compile.json','standards/injected.log','standards/shutdown-model.log','standards/storage.log','standards/doc.log','behavior/test-analysis.json','behavior/load-tests.json','report-language.log']
checks={p:(P/p).exists() for p in required}
result={'reviewed_head':cmd(['git','rev-parse','HEAD'],W),'worktree_status':cmd(['git','status','--short'],W),'main_status':cmd(['git','status','--short'],M),'main_lean_source_difference':cmd(['git','diff','3471cbe35','--','src/Effect4','src/OCaml5/Eff/Goldens.lean'],M),'language':cmd(['python3','scripts/check-language.py','--strict',str(R/'README.md')],M),'findings':{'A':a,'B':b},'branch_coverage':{r['branch']:r['branch'] in s for r in branches},'research_folder_coverage':{r['folder']:r['folder'] in s for r in research},'required_evidence':checks,'local_links':links,'readme_sha256':hashlib.sha256((R/'README.md').read_bytes()).hexdigest()}
assert len(a)<=20 and len(b)<=10 and len(a)==len(set(a)) and len(b)==len(set(b))
assert len(branches)==15 and len(research)==49
assert all(result['branch_coverage'].values()) and all(result['research_folder_coverage'].values())
assert all(checks.values()) and all(l['exists'] for l in links)
assert result['language']['exit']==0
assert result['worktree_status']['stdout']==''
assert result['main_lean_source_difference']['stdout']==''
(P/'final-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'A_findings':len(a),'B_findings':len(b),'branches':len(branches),'research_folders':len(research),'all_evidence_present':all(checks.values()),'language_exit':result['language']['exit'],'worktree_clean':result['worktree_status']['stdout']=='','main_status':result['main_status']['stdout'],'readme_sha256':result['readme_sha256']},indent=2))
