"""Check the generated C call structure without treating it as a timing theorem."""
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
source = (ROOT / '.lake/build/ir/Tools/View/Flow.c').read_text()

def body(name):
    marker = 'LEAN_EXPORT lean_object* lp_effect4_Tools_View_Flow_' + name + '('
    signature = re.search(re.escape(marker) + r'[^;{}]*\)\{', source)
    assert signature is not None, name
    begin = signature.end() - 1
    depth = 1
    end = begin + 1
    while depth:
        if source[end] == '{':
            depth += 1
        elif source[end] == '}':
            depth -= 1
        end += 1
    return source[begin:end]

prepared = body('preparePlacement')
recurrence = body('assignHeightsIndexed')
report = {
    'prepared_index_constructions': prepared.count('lp_effect4_Tools_Graph_Index_ofList___redArg('),
    'prepared_indexed_assignments': prepared.count('lp_effect4_Tools_View_Flow_assignHeightsIndexed('),
    'recurrence_index_constructions': recurrence.count('lp_effect4_Tools_Graph_Index_ofList___redArg('),
    'scope': 'Compiled call structure only; not a timing or complexity theorem.',
}
assert report['prepared_index_constructions'] == 1
assert report['prepared_indexed_assignments'] == 1
assert report['recurrence_index_constructions'] == 0
(HERE / 'inspection.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
