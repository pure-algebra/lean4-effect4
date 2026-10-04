import re, subprocess, sys, collections
rows = ['refUpdate','refGetAndUpdate','refUpdateAndGet','refUpdateSome','refGetAndUpdateSome','refUpdateSomeAndGet','refModify','refModifySome']
rowre = re.compile(r'(?<![A-Za-z_])\.?(?:SyncOp\.)?(' + '|'.join(sorted(rows, key=len, reverse=True)) + r')\b(?!_)\s+([^\s,)=|]+)\s+([^\s,)=|]+)')
interp = re.compile(r'FnName\.(total|partialUpdate|modify|modifySome)\b|\b(?:f|pf|fn)\.(total|partialUpdate|modify|modifySome)\b|\b(fits_total|fits_partialUpdate|modify_nat|modifySome_nat|nat_cell)\b|FnName\.(total|partialUpdate|modify|modifySome)_(validIn|keys)')
decl = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*(theorem|def|abbrev|instance|example|lemma|structure|inductive)\s+([^\s:(]*)')
files = subprocess.run(['git','ls-files','*.lean'],capture_output=True,text=True).stdout.split()
per = collections.OrderedDict()
for f in files:
    if f.startswith('Test/fixtures/'): continue
    cur = None; hits = []
    for i,line in enumerate(open(f, encoding='utf-8'),1):
        m = decl.match(line)
        if m: cur = m.group(2) or m.group(1)
        code = line.split('--')[0]
        a = rowre.search(code)
        # a NativeOp one-argument use looks like `.refUpdate f =>` or `(.refUpdate .incr)`: rowre needs two tokens
        b = interp.search(code)
        if a or b:
            # skip doc lines inside /-- -/ ? keep all, mark doc
            hits.append((i, cur, line.rstrip()))
    if hits: per[f] = hits
tot_decl = set(); tot_lines = 0
for f, hits in per.items():
    ds = sorted({(h[1] or '?') for h in hits})
    tot_decl |= {(f,d) for d in ds}; tot_lines += len(hits)
    print(f"{f}: {len(hits)} lines, {len(ds)} decls: {', '.join(ds)}")
print('files', len(per), 'decls', len(tot_decl), 'lines', tot_lines)
