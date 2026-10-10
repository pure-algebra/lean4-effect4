from pathlib import Path
import hashlib, json, re, subprocess
r=Path(__file__).resolve().parent
main=Path('/Users/pooks/Dev/lean4-effect4')
def git(*args):
    return subprocess.check_output(['git',*args],cwd=main)
pinned=[]
for filename,prefix in [('pins.json','snapshot'),('pins-d4c869ee.json','d4c869ee/snapshot')]:
    pins=json.loads((r/filename).read_text())
    for item in pins['files']:
        source=git('show',pins['commit']+':'+item['path'])
        assert hashlib.sha256(source).hexdigest()==item['sha256'],item['path']
        snapshot=r/prefix/item['path']
        if snapshot.exists(): assert source==snapshot.read_bytes(),item['path']
    pinned.append({'commit':pins['commit'],'files':len(pins['files'])})
rev=pins['commit']
registry=git('show',rev+':tools/ProofGraph/Registry.lean').decode()
claim=re.search(r'\{ id := "rows-denotation-driver".*?pointer := \.witness `([^ }]+)',registry,re.S)
assert claim and claim.group(1)=='Effect4.Run.runWith_denotes'
report=git('show',rev+':generated/semantics.md').decode()
assert '| rows-denotation-driver | simulation | proved | Effect4.Run.runWith_denotes |' in report
assert '| R6 | open |' in report
changed=git('diff','--name-only','b98d81c3',rev,'--','src').decode().splitlines()
assert all(p=='src/Effect4/Laws.lean' or p.startswith('src/Effect4/Laws/') for p in changed)
root=git('show',rev+':src/Effect4/Laws.lean').decode()
assert 'import Effect4.Laws.Api.HostDrive' in root
refs=git('grep','-n','-E','guardRows_meets|guardRows_of_meets|hostAnswered_guardRows|import Effect4.Laws.Program.RowProtocol',rev,'--','src','Test','tools').decode().splitlines()
entry_paths=['src/Effect4/Run.lean','src/Effect4/Laws/Author.lean','tools/Tools/ArchitectureRoles.lean']
# The compiled entry artifacts come from the existing overlay; their source is unchanged.
entry_hashes={}
review=r.parents[2]
for path in entry_paths:
    source=git('show',rev+':'+path)
    assert source==(review/path).read_bytes(),path
    entry_hashes[path]=hashlib.sha256(source).hexdigest()
out={'pinned':pinned,'registry_pointer':claim.group(1),'generated_claim':'proved','R6':'open',
     'changed_source_files':changed,'new_core_import_edges':False,'law_root_reaches_driver':True,
     'entry_sources_unchanged':entry_hashes,'row_protocol_consumers':refs}
(r/'checks-d4c869ee/source-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
