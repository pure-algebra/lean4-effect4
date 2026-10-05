from urllib.request import urlopen, Request
from pathlib import Path
import json, hashlib, datetime
r=Path(__file__).parent
sources=[('w3c-hr-time2.html','https://www.w3.org/TR/2019/REC-hr-time-2-20191121/'),('w3c-hr-time3-20260901.html','https://www.w3.org/TR/2026/WD-hr-time-3-20260901/'),('node-process-v26.10.0.html','https://nodejs.org/docs/v26.10.0/api/process.html'),('posix-clock-gettime.html','https://pubs.opengroup.org/onlinepubs/9799919799/functions/clock_gettime.html')]
records=[]
for name,url in sources:
 d={'url':url,'file':name,'retrieved_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urlopen(Request(url,headers={'User-Agent':'Effect4-design-review/1.0'}),timeout=20) as h:
   b=h.read(); d.update(status=h.status,final_url=h.url,content_type=h.headers.get('content-type'),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  (r/name).write_bytes(b)
 except Exception as e: d['error']=str(e)
 records.append(d)
(r/'download-manifest.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records,indent=2))
