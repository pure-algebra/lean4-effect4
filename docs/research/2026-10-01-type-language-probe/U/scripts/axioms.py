#!/usr/bin/env python3
"""Probe U: every axiom receipt of the probe's own declarations (`ProbeU.*`), read from the logs.

    python3 U/scripts/axioms.py            (writes U/axioms.tsv, prints the counts)
    python3 U/scripts/axioms.py <dir>      (checks only the theorems under <dir>; the red fixture
                                            U/scripts/fixtures/axioms-red must exit 1)

A declaration printed in two logs (a module and a probe that prints it again) is listed once;
the two receipts must agree, or the script refuses. Receipts of the tree's definitions printed
beside a theorem about them (`Tools.ProfileJson.tyJson`, …) are not the probe's and are skipped.
It also refuses a `theorem` declared in `U/probes` or `U/generated/ProbeU` whose receipt no log
prints (the census verifiers, which declare none, are skipped).
"""
import collections, glob, os, re, sys

U = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RX = re.compile(r"^'(.+?)' (depends on axioms: \[(.*)\]|does not depend on any axioms)$")
seen = {}
for path in sorted(glob.glob(os.path.join(U, 'logs', '*.log'))):
    for line in open(path).read().splitlines():
        m = RX.match(line)
        if not m or not m.group(1).startswith('ProbeU.'):
            continue
        name, ax = m.group(1), ('[' + m.group(3) + ']') if m.group(3) is not None else '(none)'
        if name in seen and seen[name][0] != ax:
            sys.exit(f'{name}: {seen[name][0]} in {seen[name][1]} but {ax} in {os.path.basename(path)}')
        seen.setdefault(name, (ax, os.path.basename(path)))
ONLY = sys.argv[1] if len(sys.argv) > 1 else None
if ONLY is None:
    with open(os.path.join(U, 'axioms.tsv'), 'w') as out:
        out.write('theorem\taxioms\tlog\n')
        for name in sorted(seen):
            out.write(f'{name}\t{seen[name][0]}\t{seen[name][1]}\n')
counts = collections.Counter(ax for ax, _ in seen.values())
print(f'{len(seen)} receipts: ' + ', '.join(f'{v} {k}' for k, v in sorted(counts.items(), key=lambda kv: -kv[1])))
short = {n.split('.')[-1] for n in seen}
THM = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?theorem\s+([^\s(:{\[]+)", re.M)
missing = []
if ONLY is None:
    files = sorted(glob.glob(os.path.join(U, 'probes', '**', '*.lean'), recursive=True) +
                   glob.glob(os.path.join(U, 'generated', 'ProbeU', '*.lean')))
else:
    files = sorted(glob.glob(os.path.join(os.path.abspath(ONLY), '**', '*.lean'), recursive=True))
for path in files:
    if os.path.basename(path).startswith('ProofCensus'):
        continue
    for m in THM.finditer(open(path).read()):
        if m.group(1).split('.')[-1] not in short:
            missing.append(f'{os.path.relpath(path, U)}: {m.group(1)}')
print(f'theorems declared in {len(files)} files without a printed receipt: {len(missing)}')
for x in missing:
    print('  ' + x)
sys.exit(1 if missing else 0)
