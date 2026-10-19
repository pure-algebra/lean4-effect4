import json, glob, os, re, sys
rows = []
for f in glob.glob('/Users/pooks/.claude/projects/-Users-pooks-Dev-lean4-effect4/*.jsonl'):
    try:
        for line in open(f, errors='ignore'):
            if '"type":"user"' not in line: continue
            try: o = json.loads(line)
            except Exception: continue
            if o.get('type') != 'user' or o.get('isMeta') or o.get('isSidechain'): continue
            m = o.get('message', {})
            c = m.get('content')
            texts = []
            if isinstance(c, str): texts = [c]
            elif isinstance(c, list):
                texts = [x.get('text','') for x in c if isinstance(x, dict) and x.get('type') == 'text']
            for t in texts:
                t = t.strip()
                if not t or t.startswith('<') or 'tool_use_id' in t or t.startswith('This session is being continued'): continue
                if t.startswith('[Request interrupted'): continue
                rows.append((o.get('timestamp',''), os.path.basename(f)[:8], t))
    except Exception as e:
        pass
rows.sort()
seen=set(); out=[]
for ts, sid, t in rows:
    k = t[:200]
    if k in seen: continue
    seen.add(k); out.append((ts, sid, t))
json.dump(out, open(sys.argv[1], 'w'))
print(len(out), 'distinct owner messages;', out[0][0][:10] if out else '', '..', out[-1][0][:10] if out else '')
