from pathlib import Path
import subprocess,time,json,platform
p=Path('/tmp/effect4-row-research-20260902')
rows=[]
for name in ['baseline']+[f'{mode}_{n}' for n in [8,16,32,64,128,256] for mode in ['tc','explicit']]:
    for rep in range(3):
        t=time.perf_counter()
        try:
            r=subprocess.run(['lake','env','lean',str(p/(name+'.lean'))],capture_output=True,text=True,timeout=30)
            row=dict(name=name,rep=rep,seconds=round(time.perf_counter()-t,6),exit=r.returncode,output=r.stdout+r.stderr)
        except subprocess.TimeoutExpired as e:
            row=dict(name=name,rep=rep,seconds=round(time.perf_counter()-t,6),exit='TIMEOUT',output=str(e))
        rows.append(row)
        print(json.dumps(row),flush=True)
        if row['exit']!=0: break
(p/'measurements.json').write_text(json.dumps(dict(platform=platform.platform(),rows=rows),indent=2))
