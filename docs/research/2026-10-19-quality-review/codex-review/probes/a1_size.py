#!/usr/bin/env python3
"""Source census, not a claim that every candidate requires an edit."""
import collections
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
WT = Path('/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4')
text = (WT / 'src/OCaml5/Lcnf/Builtins.lean').read_text()
rows = re.findall(r'^  row `([^\s]+).*?\.(exact|domain|approximate|unsound)\b', text, re.M | re.S)
files = subprocess.check_output(['git', '-C', str(WT), 'ls-files', 'ocaml/*.ml', 'ocaml/*.mli'], text=True).splitlines()
hand = [f for f in files if 'GENERATED' not in (WT/f).read_text() and 'tools/typed_lint/test/' not in f]
consumers = []
for file in hand:
    source = (WT/file).read_text()
    hits = [line.strip() for line in source.splitlines() if re.search(r'\b(?:Val|Lit)\.(?:Nat|NegInt|Float)\b|\b(?:Api_gen|Api_engine|Eff_types)\b', line)]
    if hits:
        consumers.append({'file':file, 'matching_lines':len(hits), 'lines':len(source.splitlines())})
generated = {}
for file in ['ocaml/eff/eff_types.ml','ocaml/gen/closure_gen.ml','ocaml/engine/api_engine.ml','ocaml/engine/test/lanes/lanes_gen.ml']:
    source = (WT/file).read_text()
    generated[file] = {'lines': len(source.splitlines()), 'int_tokens':len(re.findall(r'\bint\b',source)),
                       'integer_tokens':len(re.findall(r'(?<![\w])\d+(?![\w])',source)),
                       'saturated_literal_uses':len(re.findall(r'\bmax_int\b',source))}
fields = (HERE/'a1-fields.log').read_text().splitlines()
out = {'commit':subprocess.check_output(['git','-C',str(WT),'rev-parse','HEAD'],text=True).strip(),
       'builtin_classes':dict(collections.Counter(c for _,c in rows)), 'builtin_total':len(rows),
       'numeric_rows':[n for n,_ in rows if n.startswith(('Nat.','Int.','UInt64.','USize.')) or n in ['instDecidableEqNat','instDecidableEqUInt64']],
       'nat_field_count':sum('NAT_FIELD' in f for f in fields), 'nat_fields':[f for f in fields if 'NAT_FIELD' in f],
       'generated':generated, 'hand_consumer_candidates':consumers, 'hand_consumer_candidate_count':len(consumers),
       'scope':'Numeric tokens include non-Nat fields and indices. Consumer candidates require typed inspection; counts are not promised edit counts.'}
(HERE/'a1-size.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['hand_consumer_candidates','nat_fields']},indent=2))
