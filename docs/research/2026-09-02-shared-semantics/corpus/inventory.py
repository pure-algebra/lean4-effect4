from pathlib import Path
import subprocess, json, hashlib
root=Path('/Users/pooks/Dev/foldlab/corpus')
def git(repo,*args):
    return subprocess.check_output(['git','-C',str(repo),*args],text=True)
pinrows=[x.split('\t') for x in (root/'.pins.tsv').read_text().splitlines()]
pins={Path(x[2]).name:x for x in pinrows if x[1]}
repos=[]
for p in sorted(root.iterdir()):
    if not p.is_dir() or not (p/'.git').exists(): continue
    files=git(p,'ls-files','-z').split('\0')[:-1]
    ts=[f for f in files if f.endswith(('.ts','.tsx','.mts','.cts'))]
    package=[]
    for f in files:
        if f=='package.json' or f.endswith('/package.json'):
            try: d=json.loads((p/f).read_text())
            except (ValueError,OSError): continue
            deps={k:v for sec in ['dependencies','devDependencies','peerDependencies','optionalDependencies'] for k,v in d.get(sec,{}).items() if k=='effect' or k.startswith('@effect/')}
            if deps: package.append({'path':f,'dependencies':deps})
    filescan=[f for f in ts if not f.endswith(('.d.ts','.d.mts','.d.cts')) and not (p.name=='tim-smart_lalph' and f.startswith('repos/effect/'))]
    row={'repo':p.name,'listed':p.name in pins,'recorded_pin':pins.get(p.name,[None,None])[1],'head':git(p,'rev-parse','HEAD').strip(),'status':git(p,'status','--porcelain=v1'),'tracked_ts_family':len(ts),'declaration_ts':sum(f.endswith(('.d.ts','.d.mts','.d.cts')) for f in ts),'vendored_effect_ts':sum(f.startswith('repos/effect/') for f in ts) if p.name=='tim-smart_lalph' else 0,'analysis_files':filescan,'packages':package}
    row['pin_matches']=row['recorded_pin']==row['head'] if row['listed'] else None
    repos.append(row)
selected=[r for r in repos if r['listed']]
digest=hashlib.sha256(''.join(f"{r['repo']}\t{r['head']}\n" for r in selected).encode()).hexdigest()
out={'root':str(root),'pin_row_count':len(pinrows),'pin_unique':len(set(x[0] for x in pinrows)),'absent_listed':[x[0] for x in pinrows if not Path(x[2]).exists()],'pinlist_sha256':hashlib.sha256((root/'.pins.tsv').read_bytes()).hexdigest(),'selected_repo_pins_sha256':digest,'repos':repos}
Path('/tmp/effect-q9-research/inventory.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='repos'},indent=2))
for r in repos: print(r['repo'],r['listed'],r['head'],r['pin_matches'],r['tracked_ts_family'],r['declaration_ts'],r['vendored_effect_ts'],len(r['analysis_files']),repr(r['status']))
print('selected total',len(selected),sum(r['tracked_ts_family'] for r in selected),sum(len(r['analysis_files']) for r in selected))
