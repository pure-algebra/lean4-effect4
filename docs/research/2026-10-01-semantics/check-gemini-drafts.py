#!/usr/bin/env python3
"""Mechanical checks of the Gemini semantics drafts against the tree (coordinator, 2026-10-01).

Run from the repository root:
    python3 docs/research/2026-10-01-semantics/check-gemini-drafts.py
Exit 0 only when every check passes. Reading only; it builds nothing, and a grep is not the
semantics producer (the producer, loading the environment, is the real check of the registry).

1. registry-content.lean: every backtick-qualified name is a module path or a declaration found by
   grep; every goal pointer names a theorem concluding ProofGraph.Obligation; every register id
   and cut row exists; literature keys are reported (pending a key column in sources/README.md).
2. the documents named on the command line (default: the three Gemini drafts): every `name` followed
   on the same line by a file:line locator (plain, or a file:/// link) names a declaration within
   three lines of that line. A cell listing several names passes if any of them is there.
"""
import pathlib, re, subprocess, sys

HERE = 'docs/research/2026-10-01-semantics/'
G = HERE + 'gemini/'
fail = []

def decl_exists(leaf):
    r = subprocess.run(['grep', '-rlE', r'^\s*(@\[[^\]]*\]\s*)?(private |protected |noncomputable )*'
                        r'(theorem|def|abbrev|structure|inductive|instance|opaque|class|namespace)\s+'
                        r'([A-Za-z_.]*\.)?' + re.escape(leaf) + r'\b', 'src', 'tools', 'Test',
                        '--include=*.lean'], capture_output=True, text=True)
    return bool(r.stdout.strip())

# 1. the registry value
reg = pathlib.Path(G + 'registry-content.lean').read_text()
for n in sorted(set(re.findall(r'(?<![`\w])`([A-Z][\w.]*(?:\.\w+)+)', reg))):
    if not (pathlib.Path('src/' + n.replace('.', '/') + '.lean').exists()
            or pathlib.Path(n.replace('.', '/') + '.lean').exists() or decl_exists(n.split('.')[-1])):
        fail.append(f'registry: no declaration or module {n}')
for g in re.findall(r'pointer\s*:=\s*\.goal\s+`([\w.]+)', reg):
    out = subprocess.run(['grep', '-rhE', '-A2', r'^\s*theorem\s+' + re.escape(g.split('.')[-1]) + r'\b',
                          'src/Effect4/Laws', '--include=*.lean'], capture_output=True, text=True).stdout
    if 'ProofGraph.Obligation' not in out:
        fail.append(f'registry: goal pointer {g} is not a theorem concluding ProofGraph.Obligation')
register = pathlib.Path('Test/Counterexamples/REGISTER.md').read_text()
for i in sorted(set(re.findall(r'E4-[A-Z]+-CE-\d+', reg))):
    if f'`{i}`' not in register:
        fail.append(f'registry: register id {i} not in Test/Counterexamples/REGISTER.md')
decisions = pathlib.Path('docs/core/decisions.md').read_text()
for r in sorted(set(int(x) for x in re.findall(r'decisionRow\s*:=\s*(\d+)', reg))):
    if not re.search(rf'^\| {r} \|', decisions, re.M):
        fail.append(f'registry: decisions row {r} does not exist')
readme = pathlib.Path(HERE + 'sources/README.md').read_text()
keys = sorted(k for k in set(re.findall(r'work\s*:=\s*"([^"]+)"', reg)) if k not in readme)
claims = re.findall(r'\{\s*id\s*:=\s*"([^"]+)"\s*,\s*concept\s*:=', reg)
dups = sorted(c for c in set(claims) if claims.count(c) > 1)
if dups:
    fail.append(f'registry: duplicate claim ids {dups}')

# 2. the documents' locators
base = {}
for p in subprocess.run(['bash', '-c', "find src tools Test -name '*.lean'"],
                        capture_output=True, text=True).stdout.split():
    base.setdefault(p.split('/')[-1], []).append(p)
loc = re.compile(r'file:///(?:Users/pooks/Dev/lean4-effect4/)?((?:src|Test|tools)/[^#)\s]+\.lean)#L(\d+)'
                 r'|\(`((?:src|Test|tools)/[^`:]+\.lean|\w+\.lean):(\d+)`')
ident = re.compile(r'`([A-Za-z_][\w.]*)`')
checked = 0
DOCS = sys.argv[1:] or [G + f for f in ['semantics-v1.md', 'implementation-inventory.md', 'receipt-documentation.md']]
for f in DOCS:
    seen = set()
    for no, line in enumerate(pathlib.Path(f).read_text().split('\n'), 1):
        for m in loc.finditer(line):
            path, at = (m.group(1), int(m.group(2))) if m.group(1) else (m.group(3), int(m.group(4)))
            names = [n for n in ident.findall(line[max(0, m.start() - 160):m.start()])
                     if not n.endswith('.lean')]
            if not names or (path, at, tuple(names)) in seen:
                continue
            seen.add((path, at, tuple(names)))
            checked += 1
            files = [path] if '/' in path else base.get(path, [])
            files = [c for c in files if pathlib.Path(c).exists()]
            if not files:
                fail.append(f'{f}:{no}: no such file {path}')
                continue
            stem = path.split('/')[-1][:-5]
            ok = any(n.split('.')[-1] == stem or re.search(r'\b' + re.escape(n.split('.')[-1]) + r'\b',
                     '\n'.join(pathlib.Path(c).read_text().split('\n')[max(0, at - 4):at + 3]))
                     for n in names for c in files)
            if not ok:
                ghost = [n for n in names if not decl_exists(n.split('.')[-1])]
                why = f'no declaration named {ghost[-1]} anywhere' if ghost else 'name not within 3 lines'
                fail.append(f'{f}:{no}: `{names[-1]}` at {path}:{at}: {why}')

print(f'registry: {len(claims)} claims; document locators checked: {checked}')
if keys:
    print(f'PENDING (a key column in sources/README.md, before C6): {len(keys)} literature keys: {keys}')
for x in fail:
    print('FAIL', x)
print('PASS' if not fail else f'{len(fail)} failures')
sys.exit(1 if fail else 0)
