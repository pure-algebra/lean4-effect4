#!/usr/bin/env python3
"""Classify the files that Codex's merges added under src/Effect4/Laws and Test.

Run from the repository root:  python3 docs/research/2026-10-15-remaining-work/probes/classify.py
It reads `git diff --name-status 94bec12aa HEAD` (94bec12aa is the main line before the three
Codex merges), counts lines with the file contents at HEAD, and assigns each added file a class:
base (generic, kept), superseded (a driver's command, snapshot or settlement transport), or
casing (one program's outline and native facts). The rule is by family and, inside the four
drivers, by file name; it is a reading, not a dependency census.
"""
import collections, re, subprocess

BASE = "94bec12aa"
out = subprocess.run(["git", "diff", "--name-status", BASE, "HEAD", "--", "src/Effect4/Laws", "Test"],
                     capture_output=True, text=True, check=True).stdout
added = [line.split("\t")[1] for line in out.splitlines() if line.startswith("A")]

DRIVER = re.compile(r'(Queue|Tasks|TaskAdmission|Waits|Wait$|Settlement|Disposition|Activation|Metadata|'
                    r'Rows$|Edits|Messages|Replies|Admin|Administration|AdministrativeFields|DecisionEdits|'
                    r'Commands$|CommandStep|Driver|Decision$|Dynamic|Emission|Transport|Injection|Retirement|'
                    r'ObserverMap|PendingInstall|PendingFinalizer|Replacement|Interrupt$|QueueInterrupt|'
                    r'ConfigurationInterrupt|CleanupJoint|NativeWords|NativeQueue|NativeJoin|Recorded|'
                    r'DeferredQuiet|PendingParks|Words)')

def classify(p):
    name = p.split('/')[-1].replace('.lean', '')
    if p.startswith('src/Effect4/Laws/Machine/'): return 'base', 'Laws/Machine'
    for family in ['/CodeClosure/', '/PlaceFunding/', '/Guard/', '/CrewLogs', '/ReleaseWriter/', '/Contracts/']:
        if family in p: return 'base', family.strip('/')
    if re.search(r'/Program/Finalizer', p): return 'base', 'Finalizer*'
    if re.search(r'/Program/(Native|Primitive|Parked)', p): return 'base', 'Native*, Primitive*, Parked*'
    if '/AnswerSlots/' in p:
        for prefix in ['Allocation', 'Initialized']:
            if name.startswith(prefix):
                return ('superseded' if DRIVER.search(name) else 'base'), 'AnswerSlots ' + prefix + '*'
        return 'base', 'AnswerSlots Typed* and the rest'
    if 'Scenario/Atomic' in p: return ('superseded' if DRIVER.search(name) else 'casing'), 'Atomic scenario'
    if 'Proofs/HostTimeout' in p:
        n = name.replace('HostTimeoutNumber', '').replace('HostTimeout', '')
        return ('superseded' if DRIVER.search(n) else 'casing'), 'Timeout proofs'
    if 'QueueWorkers' in p: return 'casing', 'queue crew proofs and scenario'
    return 'casing', 'Workers proofs and others'

lines = lambda p: sum(1 for _ in open(p))
total = collections.Counter(); family = collections.defaultdict(collections.Counter)
files = collections.defaultdict(list)
for p in added:
    cls, fam = classify(p); n = lines(p)
    total[cls] += n; family[(fam, cls)][cls] += n
    files[(fam, cls)].append(f"{p.split('/')[-1][:-5]}({n})")
print("added files:", len(added), "lines:", sum(total.values()), dict(total))
for (fam, cls), c in sorted(family.items(), key=lambda kv: (kv[0][1], -sum(kv[1].values()))):
    print(f"{cls:10s} {sum(c.values()):6d} {len(files[(fam, cls)]):3d}  {fam}: {' '.join(files[(fam, cls)])}")
