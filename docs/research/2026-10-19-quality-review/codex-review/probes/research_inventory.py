from pathlib import Path
import json,re,subprocess
M=Path('/Users/pooks/Dev/lean4-effect4');W=Path('/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4');P=Path(__file__).parent
tracked=subprocess.check_output(['git','-C',str(W),'ls-files','docs/research'],text=True).splitlines()
authority_paths=['docs/core/decisions.md','docs/STATE.md','docs/ARCHITECTURE.md','docs/DESIGN-BASIS.md','docs/DESIGN-ISSUES.md']
auth={f:(W/f).read_text() for f in authority_paths}
rows=[];excerpt=[]
for d in sorted((M/'docs/research').iterdir()):
 if not d.is_dir() or not re.match(r'2026-10-1[5-8]-',d.name):continue
 mds=list(d.glob('*.md'))
 primary=sorted(mds,key=lambda f:(f.name!='README.md','receipt' not in f.name.lower(),'report' not in f.name.lower(),f.name))[:2]
 row={'folder':d.name,'tracked_files':sum(f.startswith('docs/research/'+d.name+'/') for f in tracked),'authority_citations':[f for f,t in auth.items() if d.name in t], 'notes':[str(f.relative_to(M)) for f in primary]}
 rows.append(row);excerpt.append('\n=== '+d.name+' '+json.dumps(row)+' ===')
 for f in primary:
  lines=f.read_text().splitlines();excerpt.append('FILE '+str(f.relative_to(M)))
  excerpt.extend(lines[:24])
  for i,s in enumerate(lines):
   if re.search(r'^#{1,3} .*?(?:open|verdict|result|remain|not land|status|blocked|conclusion|one thing)',s,re.I):excerpt.extend(lines[i:i+12])
(P/'research-inventory.json').write_text(json.dumps(rows,indent=2))
(P/'research-excerpts.txt').write_text('\n'.join(excerpt))
print('folders',len(rows),'tracked_files',sum(r['tracked_files'] for r in rows),'excerpt_lines',len(excerpt))
