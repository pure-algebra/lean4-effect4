from pathlib import Path
import hashlib, json, re, subprocess
r=Path(__file__).resolve().parent
main=Path('/Users/pooks/Dev/lean4-effect4')
package=Path('/Users/pooks/Dev/lean4-effects')
head='a78fcad8741d634193e568b51ab7f249c1df12e7'
package_head='bf5ab8fd26ee009abbf465821a3664ea20948a49'
def git(repo,*args):
    return subprocess.check_output(['git',*args],cwd=repo)
verified=[]
for filename,prefix in [('pins.json','snapshot'),('pins-followup.json','followup')]:
    pins=json.loads((r/filename).read_text())
    for repo in pins['repositories']:
        for item in repo['files']:
            data=git(repo['repository'],'show',repo['commit']+':'+item['path'])
            assert hashlib.sha256(data).hexdigest()==item['sha256'],item['path']
            if item.get('snapshot',True):
                assert data==(r/prefix/repo['name']/item['path']).read_bytes(),item['path']
        verified.append({'commit':repo['commit'],'files':len(repo['files'])})
# Sat and Indexed stay unchanged under the newly landed completion converse.
for path in ['Effects/Coalgebra/Sat.lean','Effects/Coalgebra/Indexed.lean']:
    assert git(package,'show',package_head+':'+path)==(r/'snapshot/effects'/path).read_bytes(),path
registry=git(main,'show',head+':tools/ProofGraph/Registry.lean').decode()
claim=re.search(r'\{ id := "rows-denotation-driver".*?pointer := \.witness `([^ }]+)',registry,re.S)
assert claim and claim.group(1)=='Effect4.Run.runWith_denotes'
report=git(main,'show',head+':generated/semantics.md').decode()
assert '| rows-denotation-driver | simulation | proved | Effect4.Run.runWith_denotes |' in report
assert '| R6 | open |' in report
for name in ['runWith_layer_denotes','sessionSystem_finished','sessionSystem_finishes']:
    assert '| `'+name+'` | proved |' in report,name
changed=git(main,'diff','--name-only','d4c869ee',head,'--','src','Test','tools').decode().splitlines()
assert changed==['Test/Api/SessionMeaning.lean','src/Effect4/Laws/Api/HostDrive.lean'],changed
root=git(main,'show',head+':src/Effect4/Laws.lean').decode()
assert 'import Effect4.Laws.Api.HostDrive' in root
manifest=json.loads(git(main,'show',head+':lake-manifest.json'))
assert any(p.get('rev')==package_head for p in manifest['packages'])
package_changed=git(package,'diff','--name-only','b0dd6079',package_head,'--','Effects').decode().splitlines()
assert set(package_changed)=={'Effects/Coalgebra.lean','Effects/Coalgebra/Indexed.lean','Effects/Coalgebra/Run.lean','Effects/Coalgebra/Sat.lean'}
for file in ['checks/build-results.json','checks-followup/build-results.json','checks-followup/probe-results.json']:
    results=json.loads((r/file).read_text())
    assert results and all(x['exit_code']==0 for x in results),file
assert {x['name'] for x in json.loads((r/'checks-followup/probe-results.json').read_text())}=={'TypedLayerControls','IndexedControls','SessionControls','Audit'}
audit=(r/'checks-followup/Audit.log').read_text().strip()
assert '0 of them modulo planned goals; 0 planned goals' in audit
out={'reviewed_effect4':head,'reviewed_effects':package_head,'source_snapshots':verified,
    'changed_effect4_sources':changed,'changed_package_modules':package_changed,
    'registry_pointer':claim.group(1),'new_R6_helpers':['runWith_layer_denotes','sessionSystem_finished','sessionSystem_finishes'],
    'R6':'open','new_core_import_edges':False,'law_root_reaches_driver':True,'axiom_audit':audit,
    'all_recorded_checks_exit_zero':True,'source_only_boundary_check':True}
(r/'checks-followup/source-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
