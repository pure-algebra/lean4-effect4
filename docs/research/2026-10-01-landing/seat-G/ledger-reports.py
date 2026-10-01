# Seat G copy (2026-10-01) of seat F's copy of the organization verifier's ledger-report reader, pointed at the seat-G worktree. Original: docs/research/2026-10-01-formal-pass/organization/verify-ledger-reports.py.
# build traces (.lake/build/lib/lean/**.trace, field "log"), as printed at the command's own
# position in the import order. Prints scope, open, proved, total, ceiling, site; then the slack.
import json, os, re, sys
root = sys.argv[1] if len(sys.argv) > 1 else "/Users/pooks/Dev/lean4-effect4-seat-G/.lake/build/lib/lean"
pat = re.compile(r'^(?P<site>\S+?):(?P<line>\d+):\d+: (?P<scope>\S+): (?P<open>\d+) open, (?P<proved>\d+) proved, (?P<total>\d+) total; ceiling (?P<ceil>\d+)')
rows = []
for dp, dn, fn in os.walk(root):
    for f in fn:
        if not f.endswith('.trace'): continue
        p = os.path.join(dp, f)
        try: d = json.load(open(p))
        except Exception: continue
        for e in d.get('log', []):
            m = e.get('message', '') if isinstance(e, dict) else ''
            for line in m.splitlines():
                mm = pat.match(line.strip())
                if mm: rows.append(mm.groupdict())
prod = [r for r in rows if r['site'].startswith('src/')]
test = [r for r in rows if not r['site'].startswith('src/')]
print(f"reports: {len(rows)} ({len(prod)} in src, {len(test)} elsewhere)")
print(f"distinct scopes in src: {len(set(r['scope'] for r in prod))}")
slack = [r for r in prod if int(r['ceil']) > int(r['open'])]
print(f"src reports with ceiling > open: {len(slack)}; slack slots: {sum(int(r['ceil'])-int(r['open']) for r in slack)}")
for r in sorted(slack, key=lambda r: (r['site'], int(r['line']))):
    print(f"  {r['site']}:{r['line']}  {r['scope']}  open {r['open']} proved {r['proved']} total {r['total']} ceiling {r['ceil']}")
openr = [r for r in prod if int(r['open']) > 0]
print("src reports with open > 0:")
for r in openr: print(f"  {r['site']}:{r['line']}  {r['scope']}  open {r['open']} proved {r['proved']} ceiling {r['ceil']}")
print("non-src reports:")
for r in sorted(test, key=lambda r: (r['site'], int(r['line']))): print(f"  {r['site']}:{r['line']}  {r['scope']}  open {r['open']} proved {r['proved']} total {r['total']} ceiling {r['ceil']}")
