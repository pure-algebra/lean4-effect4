import re, sys
# The last "<scope>: N open, M proved, T total" report of each scope in a build log.
last = {}
pat = re.compile(r'info: (\S+):\d+:\d+: (\S+): (\d+) open, (\d+) proved, (\d+) total')
for line in open(sys.argv[1], encoding='utf-8', errors='ignore'):
    m = pat.search(line)
    if m:
        last[m.group(2)] = (int(m.group(3)), int(m.group(4)), int(m.group(5)))
o = sum(v[0] for v in last.values()); p = sum(v[1] for v in last.values()); t = sum(v[2] for v in last.values())
print(f"{len(last)} scopes, {o} open, {p} proved, {t} total")
for k in sorted(last):
    if last[k][0] or k.endswith(('M3bWorld','M3bAdequacy','M3bAssembly','M6Ledger','M7','M6Edits')):
        print(k, *last[k])
