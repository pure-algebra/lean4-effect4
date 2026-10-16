"""Summarise a dune 3.24 --trace-file (canonical S-expressions): the processes by CPU time.
Usage: python3 dune_trace.py TRACE [N]
Each `process finish` event carries [start; duration] in ns and the child's rusage."""
import sys, re

def parse(data, i):
    if data[i:i+1] == b'(':
        i += 1; out = []
        while data[i:i+1] != b')':
            x, i = parse(data, i); out.append(x)
        return out, i + 1
    j = data.index(b':', i); n = int(data[i:j]); s = data[j+1:j+1+n]
    return s.decode('utf-8', 'replace'), j + 1 + n

def all_events(data):
    i = 0; out = []
    while i < len(data):
        if data[i:i+1] in (b'\n', b' '):
            i += 1; continue
        x, i = parse(data, i); out.append(x)
    return out

data = open(sys.argv[1], 'rb').read()
rows = []
for e in all_events(data):
    if not (isinstance(e, list) and len(e) > 2 and e[0] == 'process' and e[1] == 'finish'):
        continue
    wall = int(e[2][1]) / 1e9
    fd = {x[0]: x[1:] for x in e[3:] if isinstance(x, list) and x}
    ru = {k: int(v) for k, v in fd.get('rusage', [[]])[0]}
    cpu = (ru.get('user_cpu_time', 0) + ru.get('system_cpu_time', 0)) / 1e9
    args = [x for x in fd.get('process_args', [[]])[0] if isinstance(x, str)]
    tgt = [x for x in args if re.search(r'\.(ml|mli)$', x)] or args[-1:]
    prog = fd.get('prog', ['?'])[0].split('/')[-1]
    kind = 'impl' if '-impl' in args else ('intf' if '-intf' in args else ('link' if '-o' in args else ''))
    rows.append((cpu, wall, prog, kind, tgt[-1] if tgt else '', ru.get('maxrss', 0)))
rows.sort(key=lambda r: -r[0])
print(f"processes: {len(rows)}; summed CPU {sum(r[0] for r in rows):.1f} s; summed wall {sum(r[1] for r in rows):.1f} s")
by = {}
for r in rows:
    by.setdefault(r[2], [0, 0.0])
    by[r[2]][0] += 1; by[r[2]][1] += r[0]
print("by program: " + "; ".join(f"{k} {v[0]}x {v[1]:.1f}s" for k, v in sorted(by.items(), key=lambda kv: -kv[1][1])))
n = int(sys.argv[2]) if len(sys.argv) > 2 else 25
print(f"{'cpu':>7} {'wall':>7} {'rss MB':>7}  program       kind  file")
for cpu, wall, prog, kind, tgt, rss in rows[:n]:
    print(f"{cpu:7.2f} {wall:7.2f} {rss/1e6:7.0f}  {prog:13s} {kind:5s} {tgt}")
