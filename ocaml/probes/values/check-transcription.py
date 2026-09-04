#!/usr/bin/env python3
# O3 (values): check that every observation transcribed into src/OCaml5/Value.lean is
# byte for byte the row that values/out/*.tsv holds. The Lean `#guard`s check that the profile
# PREDICTS the transcribed rows; this checks that the transcribed rows are the OBSERVED ones.
# Run from the repository root, after values/run-values.sh.
import re, sys
src = open('src/OCaml5/Value.lean', encoding='utf-8').read()
obs = {}
for line in open('ocaml/probes/values/out/all.tsv', encoding='utf-8').read().splitlines()[1:]:
    w,k,n,b,j,jn = line.split('\t')
    obs[(w,k)] = (n,j)

def unesc(x): return x.replace('\\"','"').replace('\\\\','\\')

# facts: ⟨"w", "key", "native", "jsoo", prog⟩
seen=set(); bad=[]
for m in re.finditer(r'⟨\s*"(w_[a-z]+)",\s*"([A-Za-z0-9_]+)",\s*\n?\s*"((?:[^"\\]|\\.)*)",\s*\n?\s*"((?:[^"\\]|\\.)*)",', src):
    w,k,n,j = m.group(1), m.group(2), unesc(m.group(3)), unesc(m.group(4))
    seen.add((w,k))
    if (w,k) not in obs: bad.append(('missing-row',w,k)); continue
    if (n,j) != obs[(w,k)]: bad.append(('mismatch',w,k,(n,j),obs[(w,k)]))

# Printed / Hashed: ⟨"key", "native", "jsoo"⟩
for m in re.finditer(r'⟨"([A-Za-z0-9_]+)",\s*"([^"]*)",\s*"([^"]*)"⟩', src):
    k,n,j = m.groups()
    for w in ('w_float','w_compare'):
        if (w,k) in obs:
            seen.add((w,k))
            if (n,j) != obs[(w,k)]: bad.append(('mismatch',w,k,(n,j),obs[(w,k)]))

# the two physical-equality rows are asserted in prose+guards
seen.add(('w_compare','phys_tuple')); seen.add(('w_string','string_phys_eq'))
missing = sorted(set(obs) - seen)
print('observed rows:', len(obs), ' covered:', len(seen & set(obs)))
if missing: print('NOT COVERED:', missing)
if bad:
    print('BAD:')
    for x in bad: print(' ', x)
else:
    print('every transcribed row matches values/out/all.tsv')

# jsFacts
jsobs = {}
for line in open('ocaml/probes/values/out/p_jsrepr.tsv', encoding='utf-8').read().splitlines()[1:]:
    k,a,b = line.split('\t'); jsobs[k]=(a,b)
jsbad=[]; jsseen=set()
for m in re.finditer(r'⟨"([A-Za-z0-9_]+)",\s*\n?\s*"((?:[^"\\]|\\.)*)",\s*\n?\s*"((?:[^"\\]|\\.)*)",\s*\n?\s*\.', src):
    k,a,b = m.group(1), unesc(m.group(2)), unesc(m.group(3))
    if k in jsobs:
        jsseen.add(k)
        if (a,b)!=jsobs[k]: jsbad.append((k,(a,b),jsobs[k]))
for k in ('closure_4','closure_1','closure_partial','closure_table_before_call','closure_table_after_call','closure_call_gen_wrapper'):
    if k in jsobs and jsobs[k][0] in src: jsseen.add(k)
print('js rows:', len(jsobs), ' covered:', len(jsseen))
print('js not covered:', sorted(set(jsobs)-jsseen))
print('js bad:', jsbad if jsbad else 'none')
