from pathlib import Path
import importlib.util
import json
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts/lib'))
from lean_imports import header_imports, imports_of
from build_profile import imports_of as graph_imports

oracle = [json.loads(line) for line in (HERE / 'imports-oracle.log').read_text().splitlines()]
rows = []
for entry in oracle:
    path = HERE / 'cases' / Path(entry['path']).name
    actual = header_imports(path.read_text())
    rows.append({'case': path.stem, 'lean': entry['imports'], 'shared': actual,
                 'agrees': actual == entry['imports'], 'header_errors': entry['headerErrors']})
mismatches = {r['case'] for r in rows if not r['agrees']}
assert mismatches == {'quoted.lean', 'module-doc.lean', 'declaration-doc.lean'}, mismatches
known = {'Effect4.Program.Ty': ROOT / 'src/Effect4/Program/Ty.lean',
         'Effect4.Program.Native': ROOT / 'src/Effect4/Program/Native.lean'}
plain_edges = graph_imports(HERE / 'cases/ordinary.lean.txt', known)
quoted_edges = graph_imports(HERE / 'cases/quoted.lean.txt', known)
assert plain_edges == ['Effect4.Program.Ty', 'Effect4.Program.Native']
assert quoted_edges == []
# Restore the accepted control after the omitted-edge counterexample.
assert graph_imports(HERE / 'cases/ordinary.lean.txt', known) == plain_edges
expected_ty = ['Effect4.Data.Row', 'Effect4.Data.FieldOrder',
               'Effect4.Program.TyEq', 'Effect4.Program.TyVariance']
assert imports_of(ROOT / 'src/Effect4/Program/Ty.lean') == expected_ty
result = {'cases': rows, 'plain_graph_edges': plain_edges, 'quoted_graph_edges': quoted_edges,
          'production_Ty_imports': expected_ty, 'restored_plain_control': True}
(HERE / 'import-comparison.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
