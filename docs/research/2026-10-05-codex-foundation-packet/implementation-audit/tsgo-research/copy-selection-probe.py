"""Pure source/file-selection probe. Does not invoke a compiler or execute project scripts."""
import ast, hashlib, json, pathlib, tempfile
ROOT=pathlib.Path('/Users/pooks/Dev/lean4-effect4')
truth=ROOT/'harness/truth'
script=ROOT/'scripts/check-truth.py'
source=script.read_text()
tree=ast.parse(source)
names=[]
for node in ast.walk(tree):
    if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute) and node.func.attr=='copyfile':
        src=node.args[0]
        if isinstance(src,ast.BinOp) and isinstance(src.left,ast.Name) and src.left.id=='truth' and isinstance(src.right,ast.Constant):
            names.append(src.right.value)
patterns=[p for p in json.loads((truth/'tsconfig.json').read_text())['include'] if p.endswith('.typecheck.ts')]
def omitted(selected):
    with tempfile.TemporaryDirectory(prefix='copy-probe-',dir='/private/tmp/codex-effect4-overnight-monitor/2026-10-05-tsgo-research') as d:
        work=pathlib.Path(d)
        for name in selected:
            (work/name).write_bytes((truth/name).read_bytes())
        return [p for p in patterns if not list(work.glob(p))]
current=omitted(names)
repaired=omitted(names+['tuples.typecheck.ts'])
mutant=omitted([n for n in names+['tuples.typecheck.ts'] if n!='folds.typecheck.ts'])
assert current==['tuples.typecheck.ts'],current
assert repaired==[],repaired
assert mutant==['folds.typecheck.ts'],mutant
for name in patterns: assert (truth/name).is_file()
print(json.dumps({'kind':'pure-source-file-selection','commands':['python3 copy-selection-probe.py'],'compiler_executed':False,'explicit_truth_copyfiles':names,'typecheck_patterns':patterns,'current_missing':current,'candidate_copy_positive_missing':repaired,'removed_fold_mutant_missing':mutant,'assertions':6,'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [script,truth/'tsconfig.json',*(truth/n for n in patterns)]}},indent=2))
