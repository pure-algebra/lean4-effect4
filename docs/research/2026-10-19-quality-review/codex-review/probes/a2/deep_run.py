from pathlib import Path
import subprocess,time,json,struct,sys
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent))
from run_ml import compile_probe
exe=compile_probe(P/'deep.ml')
rows=[]
for n in [1000,300000,1000000,2000000]:
 j=P/f'deep-{n}.json';j.write_bytes(b'['*n+b'0'+b']'*n)
 w=P/f'deep-{n}.wire'
 out=bytearray()
 for i in range(n,0,-1):out+=b'\x0a'+struct.pack('>Q',10+19*i)+b'\x02'+struct.pack('>Q',1)+b'\x07'
 out+=b'\x0a'+struct.pack('>Q',10)+b'\x02'+struct.pack('>Q',1)+b'\x02';w.write_bytes(out)
 for mode,f in [('json',j),('mcp',j),('wire',w)]:
  t=time.monotonic()
  try:
   r=subprocess.run([exe,mode,f],capture_output=True,text=True,timeout=20);row=dict(depth=n,mode=mode,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,seconds=time.monotonic()-t)
  except subprocess.TimeoutExpired:row=dict(depth=n,mode=mode,exit='timeout',seconds=time.monotonic()-t)
  rows.append(row);print(row,flush=True)
  (P/'deep-results.json').write_text(json.dumps(rows,indent=2))
