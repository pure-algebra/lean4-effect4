from pathlib import Path
import hashlib,json,re,subprocess
r=Path(__file__).resolve().parent
main=Path('/Users/pooks/Dev/lean4-effect4')
pins=json.loads((r/'pins.json').read_text())
for item in pins['files']:
    source=subprocess.check_output(['git','show',pins['commit']+':'+item['path']],cwd=main)
    assert hashlib.sha256(source).hexdigest()==item['sha256'],item['path']
    snapshot=r/'snapshot'/item['path']
    if snapshot.exists(): assert source==snapshot.read_bytes(),item['path']
registry=subprocess.check_output(['git','show',pins['commit']+':tools/ProofGraph/Registry.lean'],cwd=main,text=True)
claim=re.search(r'\{ id := "rows-denotation-host".*?pointer := \.witness `([^ }]+)',registry,re.S)
assert claim and claim.group(1)=='Effect4.Run.denoteRows_eq_session_host'
report=subprocess.check_output(['git','show',pins['commit']+':generated/semantics.md'],cwd=main,text=True)
assert '| rows-denotation-host | simulation | proved | Effect4.Run.denoteRows_eq_session_host |' in report
assert '| R6 | open |' in report
# Read the exact commit's source imports; do not run the library gate.
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',pins['commit'],'src'],cwd=main,text=True).splitlines()
modules={p[4:-5].replace('/','.') : p for p in paths if p.endswith('.lean')}
contents={}
def content(module):
    if module not in contents:
        contents[module]=subprocess.check_output(['git','show',pins['commit']+':'+modules[module]],cwd=main,text=True)
    return contents[module]
def reachable(root):
    seen=set(); todo=[root]
    while todo:
        mod=todo.pop()
        if mod in seen or mod not in modules: continue
        seen.add(mod)
        for line in content(mod).splitlines():
            match=re.match(r'(?:public\s+|private\s+|meta\s+)*import\s+(.+)',line)
            if match: todo.extend(match.group(1).split('--')[0].split())
    return seen
core=reachable('Effect4')
assert not any(m=='Effect4.Laws' or m.startswith('Effect4.Laws.') for m in core)
laws=reachable('Effect4.Laws')
assert 'Effect4.Laws.Program.RowProtocol' in laws
# Verify consumers across the frozen production sources and batteries.
terms='guardRows_meets|guardRows_of_meets|hostAnswered_guardRows|import Effect4.Laws.Program.RowProtocol'
refs=subprocess.run(['git','grep','-n','-E',terms,pins['commit'],'--','src','Test','tools'],cwd=main,stdout=subprocess.PIPE,text=True,check=True).stdout
out={'commit':pins['commit'],'pinned_files':len(pins['files']),'registry_pointer':claim.group(1),
     'generated_report_claim':'proved','R6':'open','source_core_modules':len(core),
     'source_laws_modules':len(laws),'core_reaches_laws':False,'law_root_reaches_row_protocol':True,
     'consumer_references':refs.splitlines()}
(r/'checks/source-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
