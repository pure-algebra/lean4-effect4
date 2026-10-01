#!/usr/bin/env python3
"""Count the rows of `#exhaustive_gate` reports in a Lean log: per report (family, scope), the
matcher rows with and without a catch-all, and the distinct definitions behind each set.
    python3 Q/bin/exhaustive-count.py <log> [--list]"""
import sys, re, collections
log = open(sys.argv[1]).read().splitlines()
listing = '--list' in sys.argv
reports = []
cur = None
for line in log:
    m = re.match(r'#exhaustive_gate (\S+) \(family .*\) under (\S+): (\d+) match', line)
    if m:
        cur = {'root': m.group(1), 'scope': m.group(2), 'claimed': int(m.group(3)), 'rows': []}
        reports.append(cur); continue
    if cur is not None and line.startswith('  ') and '\tcatchAll ' in line:
        parts = line.strip().split('\t')
        holder = parts[0]
        catch = parts[-1].endswith('true')
        cur['rows'].append((holder, catch))
    elif cur is not None and not line.startswith('  '):
        cur = None
for r in reports:
    rows = r['rows']
    no = [h for h, c in rows if not c]
    yes = [h for h, c in rows if c]
    print(f"{r['root']} under {r['scope']}: {len(rows)} rows (report says {r['claimed']}); "
          f"no catch-all {len(no)} rows / {len(set(no))} definitions; "
          f"catch-all {len(yes)} rows / {len(set(yes))} definitions")
    if listing:
        print('  no catch-all:', ', '.join(sorted(set(no))))
        print('  catch-all:', ', '.join(sorted(set(yes))))
