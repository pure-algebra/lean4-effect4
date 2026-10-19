from pathlib import Path
import subprocess,json,time,struct,shutil,sys
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent))
from run_ml import compile_probe
exe=compile_probe(P/'fuzz.ml'); rows=[]
# This directory contains only transient inputs from this harness.
if (P/'fuzz-data').exists(): shutil.rmtree(P/'fuzz-data')
subprocess.run([exe,'setup'],check=True)
validpack=(P/'fuzz-data/pack/000000.pack').read_bytes()
validwal=next((P/'fuzz-data').glob('**/*.seg')).read_bytes()
validindex=(P/'fuzz-data/index').read_bytes()
def run(name,cmd,input=None,timeout=15):
 t=time.monotonic()
 try:
  r=subprocess.run(list(map(str,cmd)),input=input,capture_output=True,timeout=timeout,cwd=P)
  row=dict(name=name,command=list(map(str,cmd)),exit=r.returncode,seconds=time.monotonic()-t,stdout=r.stdout.decode(errors='replace'),stderr=r.stderr.decode(errors='replace'))
 except subprocess.TimeoutExpired as e:
  row=dict(name=name,command=list(map(str,cmd)),exit='timeout',seconds=time.monotonic()-t,stdout=(e.stdout or b'').decode(errors='replace'),stderr=(e.stderr or b'').decode(errors='replace'))
 rows.append(row);(P/(name+'.log')).write_text(json.dumps(row,indent=2));print(name,row['exit'],round(row['seconds'],3),row['stdout'][-250:],row['stderr'][-250:],flush=True)
 (P/'results.json').write_text(json.dumps(rows,indent=2))
for mode in ['frame','wire','shape','node','control','index','pack','wal','json','nat_json','mcp']:run(mode,[exe,mode])
for delta in [0,1,4,16,64,100]:
 b=validpack[:28]+struct.pack('>Q',(1<<62)-1-delta)+validpack[36:]
 f=P/f'pack-maxminus{delta}.bin';f.write_bytes(b);run(f.stem,[exe,'pack','file',f])
 f=P/f'frame-maxminus{delta}.bin';f.write_bytes(b'\x09'+struct.pack('>Q',(1<<62)-1-delta));run(f.stem,[exe,'frame','file',f])
for n in [1000,10000,50000,100000,300000]:
 f=P/f'deep-{n}.json';f.write_bytes(b'['*n+b'0'+b']'*n)
 run('json-'+str(n),[exe,'json','file',f])
 run('nat_json-'+str(n),[exe,'nat_json','file',f])
 run('mcp-'+str(n),[P.parent/'_build/default/engine/kit/bin/eff.exe','mcp'],input=f.read_bytes()+b'\n')
 out=bytearray()
 for i in range(n,0,-1):out+=b'\x0a'+struct.pack('>Q',10+19*(i-1)+19)+b'\x02'+struct.pack('>Q',1)+b'\x07'
 out+=b'\x0a'+struct.pack('>Q',10)+b'\x02'+struct.pack('>Q',1)+b'\x02'
 wf=P/f'deep-{n}.wire';wf.write_bytes(out);run('wire-'+str(n),[exe,'wire','file',wf])
