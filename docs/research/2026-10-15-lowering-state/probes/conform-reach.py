"""The Conform modules that no gate driver, route module or test reaches by import.

    python3 docs/research/2026-10-15-lowering-state/probes/conform-reach.py

The roots: the two gate drivers of `scripts/check-conform.py`, every module of `src/OCaml5`,
the three `Test` files that import `Conform`, and `tools/Tools/ProgramStructure.lean`.
"""
import re, pathlib
roots = ['tools/Conform/Effect4/Normalization.lean', 'tools/Conform/Effect4/NativeMain.lean',
         'Test/Audit/LetReturn.lean', 'Test/fixtures/ty-rule/CensusMirrorsConformLcnfMl.lean',
         'Test/fixtures/ty-rule/CensusMirrorsConformLcnfSemantics.lean',
         'tools/Tools/ProgramStructure.lean']
roots += [str(p) for p in pathlib.Path('src/OCaml5').rglob('*.lean')]
def path(mod):
    for base in ['tools', 'src']:
        p = pathlib.Path(base) / (mod.replace('.', '/') + '.lean')
        if p.exists():
            return p
seen, todo = set(), [pathlib.Path(r) for r in roots]
while todo:
    p = todo.pop()
    if p in seen:
        continue
    seen.add(p)
    for m in re.findall(r'^import\s+(\S+)', p.read_text(), re.M):
        if m.startswith(('Conform', 'OCaml5')) and path(m):
            todo.append(path(m))
lines = lambda p: sum(1 for _ in open(p))
unreached = sorted(set(pathlib.Path('tools/Conform').rglob('*.lean')) - seen)
for p in unreached:
    print(lines(p), p)
print('unreached:', len(unreached), 'modules,', sum(map(lines, unreached)), 'lines')
