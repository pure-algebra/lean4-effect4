#!/usr/bin/env python3
"""Attribute fresh Lean diagnostics; theorem-region counts do not establish required repairs."""
import argparse,json,re
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('mapping',type=Path);ap.add_argument('log',type=Path)
a=ap.parse_args();mapping=json.loads(a.mapping.read_text())
pattern=re.compile(r'^(.+\.lean):(\d+):(\d+): (error|warning|info): (.*)$');items=[]
for line in a.log.read_text().splitlines():
    match=pattern.match(line)
    if match:
        path,number,column,severity,message=match.groups()
        if Path(path).name != mapping['probe']+'.lean': continue
        number=int(number)
        declaration=next((d for d in mapping['declarations'] if d['harness_start']<=number<=d['harness_end']),None)
        source=next((s for s in mapping['line_map'] if s['harness_line']==number),None)
        items.append({'line':number,'column':int(column),'severity':severity,'message':message,
                      'source':source,'declaration':declaration})
    elif items:items[-1]['message']+='\n'+line
primary=[i for i in items if i['severity']=='error' and "declaration uses 'sorry'" not in i['message']]
names=sorted({i['declaration']['original_declaration'] for i in primary if i['declaration'] and i['declaration']['kind']=='theorem'})
print(json.dumps({'probe':mapping['probe'],
'note':'Diagnostic regions only: distinguish primary failures, propagation, harness artifacts, and necessary body repairs.',
'distinct_primary_error_theorem_regions':names,'distinct_primary_error_theorem_region_count':len(names),
'non_theorem_primary_errors':[i for i in primary if not i['declaration'] or i['declaration']['kind']!='theorem'],
'diagnostics':items},indent=2))
