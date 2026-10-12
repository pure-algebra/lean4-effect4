from pathlib import Path
import re,subprocess,json
paths=['src/Effect4/Laws/Program/SourceOpportunityPrimitive.lean','Test/Dogfood/Scenario/Atomic/WriterMachine.lean']
def headers(s):
 out={}
 for m in re.finditer(r'^(?:private )?(?:theorem|def|abbrev|structure|inductive) ([^\s({\[]+)',s,re.M):
  depth=0;i=m.end()
  while i<len(s):
   line=s[s.rfind('\n',0,i)+1:i].strip()
   if depth==0 and ((s[i:i+2]==':=' and not line.startswith(('letI ','let ','have '))) or s[i:i+5]=='where'): break
   if s[i] in '([{':depth+=1
   if s[i] in ')]}':depth-=1
   i+=1
  name=m.group(1);out.setdefault(name,[]).append(s[m.start():i].rstrip())
 return out
report={}
for path in paths:
 before=subprocess.check_output(['git','show','914916f0d:'+path],text=True);after=Path(path).read_text()
 old=headers(before);new=headers(after);changed=[name for name,val in old.items() if new.get(name)!=val]
 report[path]={'retained':sum(map(len,old.values())),'changed_headers':changed,'before_lines':len(before.splitlines()),'after_lines':len(after.splitlines())}
 assert not changed,(path,changed)
print(json.dumps(report,indent=2))
