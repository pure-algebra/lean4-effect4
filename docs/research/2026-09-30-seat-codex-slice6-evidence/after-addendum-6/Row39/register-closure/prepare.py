from pathlib import Path
import difflib, hashlib, json, re, subprocess

repo = Path('/Users/pooks/Dev/lean4-effect4-slice6')
out = Path('/private/tmp/row39-series/register-closure')
pin = 'd554cd7194f54c1ed2ffd020b4dc59d573bc1c34'
head = subprocess.check_output(['git','rev-parse','HEAD'], cwd=repo, text=True).strip()
paths = ['Test/Counterexamples/REGISTER.md','Test/Counterexamples/Archive/REGISTER.md']
base = {p: (repo/p).read_text() for p in paths}
state = dict(base)
sha = lambda t: hashlib.sha256(t.encode()).hexdigest()
row_re = re.compile(r'^\| `(E4-[^`]+)` \|')
rows = {m.group(1): (i,line) for i,line in enumerate(base[paths[0]].splitlines(),1) if (m:=row_re.match(line))}
archive_ids = {m.group(1) for line in base[paths[1]].splitlines() if (m:=row_re.match(line))}
numid = lambda n: f'E4-SCHEMA-CE-{n:03}'
stages = [('01-effectful-field',list(range(49,56))),('02-check-accepts-image',list(range(18,23))+list(range(43,49))+list(range(56,59)))]
mixed = {numid(17): 'Test/Counterexamples/Schema/SemanticTagSeparation.lean',numid(59):'Test/Counterexamples/Schema/Codec.lean'}
manifest = {'captured_head':head,'source_revision':pin,'repository_mutated':False,'base_hashes':{p:sha(v) for p,v in base.items()},'stages':[],'mixed_rows':[]}
original=[]
for stage, numbers in stages:
    ids=[numid(n) for n in numbers]
    assert not set(ids)&archive_ids
    before = dict(state)
    moved = [rows[i][1] for i in ids]
    selected_paths = sorted(set(p for row in moved for p in re.findall(r'`(Test/[^`]+\.lean)`',row)))
    pins=[]
    for p in selected_paths:
        blob=subprocess.check_output(['git','rev-parse',f'{pin}:{p}'],cwd=repo,text=True).strip()
        subprocess.check_call(['git','cat-file','-e',f'{pin}:{p}'],cwd=repo)
        pins.append({'path':p,'revision':pin,'blob':blob})
    state[paths[0]]='\n'.join(line for line in state[paths[0]].splitlines() if not ((m:=row_re.match(line)) and m.group(1) in ids))+'\n'
    if stage.startswith('01'):
        old='The rows of [`../REGISTER.md`](../REGISTER.md) whose witness no longer lives in\nthis tree, moved here on 2026-09-13 so that the live register lists only what a\nbattery on `main` checks. Stable IDs are never reused, so every ID cited in a\n'
        new='Rows from [`../REGISTER.md`](../REGISTER.md) whose named witness no longer lives\nin this tree are kept here so that the live register lists what a battery on\n`main` checks. The first split was on 2026-09-13; later retirements have dated\nsections below. Stable IDs are never reused, so every ID cited in a\n'
        assert old in state[paths[1]]
        state[paths[1]]=state[paths[1]].replace(old,new,1)
        label='EffectfulField'
    else:
        label='Check, Accepts, Image and Schema attack batteries'
        for id,p in mixed.items():
            old=rows[id][1]
            new=old.replace(f'`{p}`',f'`git:{pin}:{p}`',1)
            assert old in state[paths[0]]
            state[paths[0]]=state[paths[0]].replace(old,new,1)
            manifest['mixed_rows'].append({'id':id,'original_line':rows[id][0],'original_row':old,'proposed_row':new,'retired_path':p,'revision':pin})
            subprocess.check_call(['git','cat-file','-e',f'{pin}:{p}'],cwd=repo)
    section=f'## Row 39 retired witnesses: {label} (2026-10-01)\n\n'
    section+='These rows moved with row 39\'s deletion of their named attack batteries.\nThe rows below retain their original text and status; this move is no new\nsemantic ruling, repair or claim that all related checks have disappeared.\nTheir witness paths are historical and are read at the following immutable\nsources:\n\n'
    section+=''.join(f'- `git:{pin}:{p}`\n' for p in selected_paths)+'\n'
    section+='| ID | Status | Attacked statement | Witness / evidence | Forced repair |\n| --- | --- | --- | --- | --- |\n'+'\n'.join(moved)+'\n\n'
    anchor='## Historical notes\n'
    assert state[paths[1]].count(anchor)==1
    state[paths[1]]=state[paths[1]].replace(anchor,section+anchor,1)
    dest=out/stage
    dest.mkdir(exist_ok=True)
    patch=''
    for p in paths:
        patch+=f'diff --git a/{p} b/{p}\n'+''.join(difflib.unified_diff(before[p].splitlines(keepends=True),state[p].splitlines(keepends=True),fromfile='a/'+p,tofile='b/'+p))
        q=dest/'files'/p
        q.parent.mkdir(parents=True,exist_ok=True)
        q.write_text(state[p])
    (dest/'register.patch').write_text(patch)
    entry={'stage':stage,'ids':ids,'count':len(ids),'source_pins':pins,'changes':[{'path':p,'old_sha256':sha(before[p]),'new_sha256':sha(state[p])} for p in paths]}
    manifest['stages'].append(entry)
    (dest/'inventory.json').write_text(json.dumps(entry,indent=2)+'\n')
    for id in ids:
        original.append({'id':id,'source_register':paths[0],'captured_head':head,'original_line':rows[id][0],'original_row':rows[id][1]})
        assert state[paths[1]].splitlines().count(rows[id][1])==1
        assert rows[id][1] not in state[paths[0]].splitlines()
    archive_ids.update(ids)

# Every retired witness path remaining in a live register row is explicitly historical.
deleted=set()
for stage,_ in stages:
    for c in json.loads((out.parent/stage/'inventory.json').read_text())['changes']:
        if c['action']=='delete': deleted.add(c['path'])
residual=[]
for ln,line in enumerate(state[paths[0]].splitlines(),1):
    if not row_re.match(line): continue
    for p in re.findall(r'`([^`]+)`',line):
        if p in deleted: residual.append({'line':ln,'path':p})
assert not residual, residual
for id in [*map(numid,range(49,56)),*map(numid,list(range(18,23))+list(range(43,49))+list(range(56,59))),*mixed]:
    combined=state[paths[0]]+state[paths[1]]
    assert len(re.findall(r'^\| `'+re.escape(id)+r'` \|',combined,re.M))==1,id

(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(out/'original-rows.json').write_text(json.dumps(original,indent=2)+'\n')
projected=out/'projected'
projected.mkdir(exist_ok=True)
for p,v in base.items():
    q=projected/p;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(v)
checks=[]
for stage,_ in stages:
    patch=out/stage/'register.patch'
    for args in [['git','apply','--check',str(patch)],['git','apply',str(patch)]]:
        r=subprocess.run(args,cwd=projected,text=True,capture_output=True)
        assert r.returncode==0,(args,r.stdout,r.stderr)
        checks.append({'cwd':str(projected),'command':args,'exit':r.returncode,'output':r.stdout+r.stderr})
for p in paths: assert (projected/p).read_text()==state[p]
r=subprocess.run(['git','apply','--check',str(out/stages[0][0]/'register.patch')],cwd=repo,text=True,capture_output=True)
assert r.returncode==0,(r.stdout,r.stderr)
checks.append({'cwd':str(repo),'command':['git','apply','--check',str(out/stages[0][0]/'register.patch')],'exit':r.returncode,'output':r.stdout+r.stderr})
assert all((repo/p).read_text()==base[p] for p in paths),'repository register changed'
(out/'checks.json').write_text(json.dumps({'checks':checks,'verbatim_moved_rows':len(original),'retired_live_path_references':residual,'new_id_duplicates':0,'repository_register_bytes_unchanged':True},indent=2)+'\n')
print(json.dumps({'head':head,'stage_counts':{s['stage']:s['count'] for s in manifest['stages']},'mixed_rows_kept_live':list(mixed),'static_checks':'pass','output':str(out)},indent=2))
