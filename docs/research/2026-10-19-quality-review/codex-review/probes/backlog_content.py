from pathlib import Path
import subprocess,json
W=Path('/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4');P=Path(__file__).parent/'backlog'
def git(*args):return subprocess.check_output(['git','-C',str(W),*args],text=True)
rows=[]
for r in json.loads((P/'branches.json').read_text()):
 b=r['head'];base=git('merge-base','HEAD',b).strip(); paths=git('diff','--name-only',base,b).splitlines()
 same=[];other=[];dogsame=[]
 for path in paths:
  if subprocess.run(['git','-C',str(W),'diff','--quiet','HEAD',b,'--',path]).returncode==0:same.append(path)
  else:other.append(path)
  if subprocess.run(['git','-C',str(W),'diff','--quiet','codex/vessel-dogfood',b,'--',path]).returncode==0:dogsame.append(path)
 row={'branch':r['branch'],'head':b,'merge_base':base,'identical_to_review':same,'different_to_review':other,'identical_to_vessel_dogfood':dogsame,'cherry':git('cherry','HEAD',b).splitlines()};rows.append(row)
 print(r['branch'],len(same),'identical',len(other),'different',len(dogsame),'identical to dogfood', 'patch equivalents',sum(x.startswith('-') for x in row['cherry']))
(P/'content-comparison.json').write_text(json.dumps(rows,indent=2))
