from pathlib import Path
import json, subprocess, xml.etree.ElementTree as ET

root = Path.cwd()
exe = root / '.lake/build/bin/effect4'
out = root / '.lake/view-graph-command/commands-final'
base = ['inspect','--group','todo','--session','TodoApp']

def run(args, expected=0):
    result = subprocess.run([str(exe),*args],text=True,capture_output=True)
    assert result.returncode == expected, (args,result.returncode,result.stdout,result.stderr)
    print('PASS',expected,'effect4',' '.join(args))
    return result

for what in ['relations','boundary','calls','layers']:
    for form in ['md','json','svg','tsv']:
        folder=out / what / form
        run(base+['--what',what,'--form',form,'--out',str(folder)])
        files=list(folder.glob('*'))
        assert files or form == 'svg'
        if form=='json':
            doc=json.loads((folder/'todo.gen.json').read_text())
            assert doc['format']=='effect4-document/1'
        if form=='svg':
            for f in files: assert ET.parse(f).getroot().tag.endswith('svg')
    doc=json.loads((out/what/'json/todo.gen.json').read_text())
    figures=[b for b in doc['body'] if b['kind']=='graph']
    assert len(figures)==len(list((out/what/'svg').glob('*.svg')))

for args in [
    ['--what','relations','--form','png'],
    ['--what','relations','--form','svg'],
    ['--what','relations','--form','tsv'],
    ['--what','relations','--form'],
    ['--what','relations','--json','--form','md'],
    ['--what','relations','--out','--form','md'],
    ['--what','relations','--session'],
    ['--what','graph','--form','svg'],
]: run(['inspect','--group','todo',*args],2)

refused=out/'refused'
refused.mkdir(parents=True,exist_ok=True)
(refused/'todo.gen.json').write_text('keep')
run(['inspect','--group','todo','--what','relations','--form','json','--session','missing',
    '--out',str(refused)],1)
assert (refused/'todo.gen.json').read_text()=='keep'
assert list(refused.iterdir())==[refused/'todo.gen.json']
stale=out/'stale'
stale.mkdir(parents=True,exist_ok=True)
run(base+['--what','boundary','--form','svg','--out',str(stale)])
assert len(list(stale.glob('todo.*.gen.svg')))==2
keepers=['todo2.keep.gen.svg','todo%2Eother.keep.gen.svg','todo.keep.gen.tsv','todo.notes.svg','ordinary.txt']
for name in keepers: (stale/name).write_text('keep')
(stale/'todo.old.gen.svg').write_text('old')
run(base+['--what','layers','--form','svg','--out',str(stale)])
assert sorted(p.name for p in stale.iterdir())==sorted(keepers)
assert all((stale/name).read_text()=='keep' for name in keepers)
(stale/'todo.old.gen.svg').write_text('old')
before={p.name:p.read_bytes() for p in stale.iterdir()}
run(['inspect','--group','todo','--what','layers','--form','svg','--session','missing','--out',str(stale)],1)
assert {p.name:p.read_bytes() for p in stale.iterdir()}==before
multi=run(['inspect','--group','corpus','--what','relations','--form','json'],2)
assert multi.stdout=='' and '--out DIR' in multi.stderr
legacy=run(['inspect' ,'--group','todo','--what','graph','--json'])
assert json.loads(legacy.stdout)
print('PASS document selections/forms, SVG XML, usage refusals, session refusal without writes, legacy JSON')

# The command's relation TSVs are projections of the same JSON table cells.
def shown(inline):
    return next(inline[k] for k in ['text','code','label','status'] if k in inline)

def escaped(s):
    return s.replace('\\','\\\\').replace('\t','\\t').replace('\r','\\r').replace('\n','\\n')

doc=json.loads((out/'relations/json/todo.gen.json').read_text())
counts=[]
for relation in ['nodes','defs','rows','calls']:
    part=next(b for b in doc['body'] if b.get('key')=='relation-'+relation)
    table=part['body'][0]
    expected=[table['headers']]+[[ ''.join(map(shown,cell)) for cell in row] for row in table['rows']]
    actual=(out/'relations/tsv'/f'todo.relation-{relation}.gen.tsv').read_text()
    assert actual==''.join('\t'.join(map(escaped,row))+'\n' for row in expected)
    counts.append(len(table['rows']))
assert counts==[70,5,9,14]
print('PASS JSON/TSV relation equality:',counts)

corpus=out/'corpus'
run(['inspect','--group','corpus','--what','relations','--form','json','--out',str(corpus)])
files=list(corpus.glob('*.gen.json'))
assert len(files)==8
assert all(json.loads(f.read_text())['format']=='effect4-document/1' for f in files)
print('PASS eight separate corpus documents')
