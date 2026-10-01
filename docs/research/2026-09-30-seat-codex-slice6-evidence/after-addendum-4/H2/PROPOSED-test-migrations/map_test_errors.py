#!/usr/bin/env python3
"""Map actual compiler diagnostics to existing test declaration regions; do not repair."""
import argparse,json,re
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('log',type=Path)
ap.add_argument('--root',default='/Users/pooks/Dev/lean4-effect4-slice6',type=Path)
a=ap.parse_args();cache={};items=[]
def inventory(path):
    ns=[];decls=[];lines=path.read_text().splitlines()
    for number,line in enumerate(lines,1):
        if line.startswith('namespace '):ns.append(line[10:].strip())
        elif line.startswith('end ') and ns:ns.pop()
        match=re.match(r'^(?:private |protected )?(theorem|def|inductive|structure|abbrev) ([^\s(:]+)',line)
        if match:
            if decls:decls[-1]['end']=number-1
            kind,name=match.groups();decls.append({'kind':kind,'name':'.'.join(ns+[name]),'start':number})
    if decls:decls[-1]['end']=len(lines)
    return decls
for line in a.log.read_text().splitlines():
    m=re.match(r'^(.+\.lean):(\d+):(\d+): (error|warning|info): (.*)$',line)
    if m:
        filename,number,column,severity,message=m.groups();path=Path(filename)
        if not path.is_absolute():path=a.root/path
        if path.exists():
            if path not in cache:cache[path]=inventory(path)
            d=next((d for d in cache[path] if d['start']<=int(number)<=d['end']),None)
        else:d=None
        items.append({'file':str(path),'line':int(number),'column':int(column),'severity':severity,'message':message,'declaration':d})
    elif items:items[-1]['message']+='\n'+line
names=sorted({i['declaration']['name'] for i in items if i['severity']=='error' and i['declaration'] and "declaration uses 'sorry'" not in i['message']})
print(json.dumps({'note':'Regions only; distinguish proof failures, propagation, and declaration errors before counting. No test-body exemption from the strict cap is assumed.',
'existing_declaration_regions':names,'distinct_count':len(names),'diagnostics':items},indent=2))
