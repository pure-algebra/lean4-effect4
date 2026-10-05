from pathlib import Path
import urllib.request, hashlib,json,datetime
base=Path('/private/tmp/codex-effect4-overnight-monitor/2026-10-05-transactions-task-review/literature/stm')
items=[('harris-2005-composable-memory-transactions.pdf','https://www.microsoft.com/en-us/research/wp-content/uploads/2005/01/2005-ppopp-composable.pdf'),('guerraoui-kapalka-2008-opacity.pdf','https://kapalka.eu/files/opacity-ppopp08.pdf'),('ghc-9.12.2-STM.h','https://raw.githubusercontent.com/ghc/ghc/ghc-9.12.2-release/rts/STM.h'),('ghc-9.12.2-STM.c','https://raw.githubusercontent.com/ghc/ghc/ghc-9.12.2-release/rts/STM.c'),('ghc-9.12.2-Sync.hs','https://raw.githubusercontent.com/ghc/ghc/ghc-9.12.2-release/libraries/ghc-internal/src/GHC/Internal/Conc/Sync.hs')]
results=[]
for name,url in items:
 r={'name':name,'url':url,'retrievedUTC':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Codex source research'}),timeout=20) as response:
   data=response.read();r.update({'finalURL':response.url,'contentType':response.headers.get('Content-Type'),'lastModified':response.headers.get('Last-Modified'),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'path':str(base/name)})
  (base/name).write_bytes(data)
 except Exception as e:r['error']=str(e)
 results.append(r)
 print(json.dumps(r),flush=True)
(base/'downloads.json').write_text(json.dumps(results,indent=2)+'\n')
