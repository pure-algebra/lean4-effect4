from pathlib import Path
import subprocess,time,json
p=Path('/tmp/effect4-row-research-20260902')
rows=[]
for mode in ['tc','explicit']:
    source=(p/f'{mode}_256.lean').read_text().replace('open Effects','set_option maxRecDepth 2048\nopen Effects')
    path=p/f'{mode}_256_depth2048.lean'; path.write_text(source)
    for rep in range(3):
        t=time.perf_counter(); r=subprocess.run(['lake','env','lean',str(path)],capture_output=True,text=True,timeout=30)
        row=dict(name=path.stem,rep=rep,seconds=round(time.perf_counter()-t,6),exit=r.returncode,output=r.stdout+r.stderr)
        rows.append(row); print(json.dumps(row),flush=True)
        if r.returncode: break
pre=(p/'baseline.lean').read_text()
for name,src in [
    ('def_transparency','def row : Signature := atom 0 ⊕ₛ atom 1\ndef witness : Has (atom 0) row := inferInstance\n'),
    ('left_associated','abbrev row : Signature := (atom 0 ⊕ₛ atom 1) ⊕ₛ atom 2\ndef witness : Has (atom 0) row := inferInstance\n'),
    ('missing_member','abbrev row : Signature := atom 0 ⊕ₛ atom 1\ndef witness : Has (atom 2) row := inferInstance\n')]:
    path=p/(name+'.lean');path.write_text(pre+src)
    t=time.perf_counter();r=subprocess.run(['lake','env','lean',str(path)],capture_output=True,text=True,timeout=30)
    row=dict(name=name,seconds=round(time.perf_counter()-t,6),exit=r.returncode,output=r.stdout+r.stderr)
    rows.append(row);print(json.dumps(row),flush=True)
(p/'extended_measurements.json').write_text(json.dumps(rows,indent=2))
