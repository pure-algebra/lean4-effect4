import subprocess, re, json, sys
from pathlib import Path
base = '0b57d3562'
head = sys.argv[1] if len(sys.argv) > 1 else None
paths = ['src/Effect4/Laws/Machine/StoresLaws.lean', 'src/Effect4/Laws/Store/Names.lean']
foundation = 'src/Effect4/Laws/Machine/StoreValidity.lean'
def declarations(s):
 out={}
 pat=re.compile(r'^(?:protected |private |noncomputable )?(theorem|def|abbrev|inductive|structure|proof_goal|class|instance)\s+([A-Za-z_][A-Za-z_0-9.\']*)',re.M)
 matches=list(pat.finditer(s))
 for i,m in enumerate(matches):
  if s[m.start():m.end()].startswith('private '):continue
  if m.group(1)=='instance' and m.group(2) not in {'algebraCore','algebraEvaluator','wakeEvaluator','MaskKept.decidable','MaskRuns.decidable'}:continue
  end=matches[i+1].start() if i+1<len(matches) else len(s)
  raw=s[m.start():end]
  depth=0; stop=len(raw)
  for j,c in enumerate(raw):
   if c in '({[⦃':depth+=1
   elif c in ')}]⦄':depth-=1
   if depth!=0:continue
   if raw[j:j+2]==':=':
    line=raw[raw.rfind('\n',0,j)+1:j]
    if re.search(r'\bletI?\b',line):continue
    stop=j;break
   if raw[j:j+5]=='where' and (j==0 or raw[j-1].isspace()):stop=j;break
   if c=='|' and raw[raw.rfind('\n',0,j)+1:j].strip()=='':stop=j;break
  raw=raw[:stop]
  out[m.group(2)]=dict(kind=m.group(1),header=' '.join(raw.split()))
 return out

def source(path, rev=None):
 return subprocess.check_output(['git','show',rev+':'+path],text=True) if rev else Path(path).read_text()
a={};b={};counts={}
for path in paths:
 before=source(path,base);after=source(path,head)
 counts[path]={'beforeLines':len(before.splitlines()),'afterLines':len(after.splitlines())}
 for name, value in declarations(before).items(): a[(path,name)]=value
 for name, value in declarations(after).items(): b[(path,name)]=value
fresh=source(foundation,head)
counts[foundation]={'beforeLines':0,'afterLines':len(fresh.splitlines())}
moved=['Stores.handleValid','Val.validIn','Val.validInList','Val.validInList_eq_all']
for name,value in declarations(fresh).items():
 assert name in moved,name
 b[(paths[0],name)]=value
assert a==b,[(key,a.get(key),b.get(key)) for key in a.keys()|b.keys() if a.get(key)!=b.get(key)]
original=source(paths[0],base)
def chunk(s,start,end):return s[s.index(start):s.index(end,s.index(start))]
handle=chunk(original,'def Stores.handleValid','mutual')
assert chunk(fresh,'def Stores.handleValid','mutual')==handle
valid=chunk(original,'def Val.validIn','end\n')
assert chunk(fresh,'def Val.validIn','end\n')==valid
start='theorem Val.validInList_eq_all'
oldlist=chunk(original,start,'theorem Val.validIn_list').rstrip()
# The old final declaration ends before the next theorem, with no intervening documentation.
newlist=chunk(fresh,start,'end Effect4.Machine').rstrip()
assert oldlist==newlist,(oldlist,newlist)
print(json.dumps({'base':base,'head':head,'publicHeaders':len(a),'unchangedHeaders':len(a),
 'movedUnchanged':moved,'files':counts},indent=2))
