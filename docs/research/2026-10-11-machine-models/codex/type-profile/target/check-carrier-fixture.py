from pathlib import Path
import os, subprocess, sys
root=Path('/Users/pooks/.codex/worktrees/last-planned-goals/lean4-effect4')
env=os.environ.copy();env['LEAN_NUM_THREADS']='3';env['LEAN_PATH']='/private/tmp'+(':'+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
def run(label,args,expected=0):
    log=Path('/private/tmp/carrier-fixture-'+label+'.log')
    with log.open('w') as out:
        print('COMMAND:', ' '.join(args),file=out,flush=True)
        r=subprocess.run(args,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
    print(label,r.returncode,flush=True)
    if (r.returncode==0)!=(expected==0):
        print(log.read_text());sys.exit(1)
    return log
run('compile',['lake','env','lean','--root=/private/tmp','-DwarningAsError=true','-o','/private/tmp/CarrierFixture.olean','/private/tmp/CarrierFixture.lean'])
base=['lake','env','lean','-DwarningAsError=true','--run','src/OCaml5/Tools/LcnfGen.lean','--import','CarrierFixture','--cap','30','--types','CarrierFixture.Holder','--prelude','/private/tmp/carrier-fixture-prelude.ml']
for label,roots,externs,expected in [
 ('positive',['CarrierFixture.make','CarrierFixture.remark'],'/private/tmp/carrier-fixture-externs.txt',0),
 ('missing',['CarrierFixture.make'],'/private/tmp/carrier-fixture-missing.txt',1),
 ('nonempty',['CarrierFixture.nonempty'],'/private/tmp/carrier-fixture-externs.txt',1)]:
    if label=='missing': Path(externs).write_text('type CarrierFixture.Queue @int D.t\n')
    output='/private/tmp/Carrier_'+label+'.ml'
    genlog=run(label+'-generate',base+['--externs',externs,'--out',output]+roots,1 if label=='nonempty' else 0)
    if label=='nonempty':
        if 'extern rows no declaration hit (a stale ledger): [ops D.t#empty]' not in genlog.read_text():
            raise RuntimeError('nonempty control did not reach the unused empty-operation check')
        continue
    log=run(label+'-ocaml',['opam','exec','--switch=effect4','--','ocamlc','-w','+8','-warn-error','+8','-c',output],expected)
    if expected:
        text=log.read_text()
        if 'D.t' not in text or 'list' not in text:
            raise RuntimeError('negative control failed outside the carrier type boundary: '+label)
print('PASS carrier fixture: full record and existing fields retained; missing empty and nonempty list rejected',flush=True)
