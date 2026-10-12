from pathlib import Path
import re,subprocess,json,hashlib
root=Path.cwd()
paths=['src/Effect4/Laws/Machine/Clauses.lean', 'Test/Dogfood/Proofs/HostTimeoutNumberFlow.lean', 'docs/research/2026-10-11-machine-models/codex/callback-loop/TimeoutReadyEntryProbe.lean']
def headers(s):
 result={}
 for m in re.finditer(r'^(?:private )?(?:theorem|def|abbrev|structure|inductive) ([^\s({\[]+)',s,re.M):
  depth=0;i=m.end()
  while i<len(s):
   if depth==0 and (s[i:i+2]==':=' or s[i:i+5]=='where' or re.match(r'\n[ \t]*\|', s[i:])): break
   if s[i] in '([{':depth+=1
   if s[i] in ')]}':depth-=1
   i+=1
  name=m.group(1)
  key=name if name not in result else name+'@'+str(m.start())
  result[key]=s[m.start():i].rstrip()
 return result
report={}
for path in paths:
 before=subprocess.check_output(['git','show','HEAD:'+path],text=True)
 after=(root/path).read_text();old=headers(before);new=headers(after)
 changed=[n for n,h in old.items() if new.get(n)!=h]
 assert not changed,(path,changed)
 report[path]={'before_lines':len(before.splitlines()),'after_lines':len(after.splitlines()),'retained_headers':len(old),'added_names':sorted(set(new)-set(old)),'sha256':hashlib.sha256(after.encode()).hexdigest()}
print(json.dumps(report,indent=2))
