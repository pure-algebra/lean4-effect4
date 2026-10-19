from pathlib import Path
import subprocess,json,time,struct
P=Path(__file__).resolve().parent
exe=P/'fuzz.exe'
rows=[]
def run(name,cmd,timeout=20,input=None):
 t=time.monotonic()
 try:
  r=subprocess.run(list(map(str,cmd)),input=input,capture_output=True,timeout=timeout,cwd=P)
  row=dict(name=name,command=list(map(str,cmd)),exit=r.returncode,seconds=time.monotonic()-t,stdout=r.stdout.decode(errors='replace'),stderr=r.stderr.decode(errors='replace'))
 except subprocess.TimeoutExpired as e:
  row=dict(name=name,command=list(map(str,cmd)),exit='timeout',seconds=time.monotonic()-t,stdout=(e.stdout or b'').decode(errors='replace'),stderr=(e.stderr or b'').decode(errors='replace'))
 rows.append(row);(P/(name+'.log')).write_text(json.dumps(row,indent=2));print(name,row['exit'],round(row['seconds'],3),row['stdout'][-180:],row['stderr'][-180:],flush=True)
for mode in ['frame','wire','shape','node','control','index','pack','wal','json','nat_json','mcp']:
 run(mode,[exe,mode])
# Header with a positive length whose later addition wraps, not one rejected by read_be64.
pack=(P/'fuzz-data/pack/000000.pack').read_bytes()
# Restore head from the literal defined by e4_pack, with a valid CRC through setup.
subprocess.run([str(exe),'setup'],check=True)
pack=(P/'fuzz-data/pack/000000.pack').read_bytes()
for delta in [0,1,4,16,64,100]:
 b=pack[:28]+struct.pack('>Q',(1<<62)-1-delta)+pack[36:]
 f=P/f'pack-maxminus{delta}.bin';f.write_bytes(b);run(f.stem,[exe,'pack','file',f])
for n in [1000,10000,50000,100000,300000]:
 f=P/f'deep-{n}.json';f.write_bytes(b'['*n+b'0'+b']'*n)
 run('json-'+str(n),[exe,'json','file',f])
 run('mcp-'+str(n),[P.parent/'_build/default/engine/kit/bin/eff.exe','mcp'],input=f.read_bytes()+b'\n')
 # Wire Ty.Option repeated, each ctor has a ten byte encoded ordinal.
 out=bytearray()
 for i in range(n,0,-1):out+=b'\x0a'+struct.pack('>Q',10+19*(i-1)+19)+b'\x02'+struct.pack('>Q',1)+b'\x07'
 out+=b'\x0a'+struct.pack('>Q',10)+b'\x02'+struct.pack('>Q',1)+b'\x02'
 wf=P/f'deep-{n}.wire';wf.write_bytes(out);run('wire-'+str(n),[exe,'wire','file',wf])
(P/'fuzz-results.json').write_text(json.dumps(rows,indent=2))
