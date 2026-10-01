#!/usr/bin/env python3
"""Conservativity of an alphabet append (DI-47, R3.8), as one command. Seat Q, 2026-10-01.

    conservativity.py BASE [CAND]           CAND a revision; omitted: the working tree
    conservativity.py BASE --cand-dir DIR   the candidate's files read from DIR (the self-test)
    conservativity.py --self-test           the red and green controls (fixtures/conservativity)

Properties. Reads committed files only (git blobs, or the candidate's files); runs no producer
and no build: it is the check that follows the producers of the append commit, so the inputs it
judges are the regenerated groups. Each clause prints PASS or REFUSE with the paths and names it
judged; the exit code is 0 only when every clause passes (1 on a refusal, 2 on a usage error).

  C1 goldens:   every byte vector at BASE (`.bin .json .ty .hex` under the golden directories,
                and every file of the Test/fixtures/baseline/<commit>/ directories) is byte-identical in CAND, unless
                CAND's policy names it (vector_migrations / vector_removals); new vectors are
                listed as additions.
  C2 alphabets: tools/Effect4Gen/wire-tags.json: every BASE row (active or retired) keeps its
                tag; a tag is never given twice; an active row may leave only into `retired`.
                The generated manifests (ocaml/eff/eff_manifest.txt, ocaml/goldens/eff/
                manifest.txt, ocaml/goldens/eff/wire-tags.txt): each BASE family line is a
                prefix of CAND's (names and argument shapes), so an existing constructor is
                neither moved nor re-typed.
  C3 verdicts:  generated/corpus-index.tsv (Lean's wellTyped/readable verdict per program),
                ocaml/eff/goldens/corpus.txt (the golden programs' typing verdicts),
                harness/truth/corpus-results.tsv (the host lane, as committed): every BASE row is
                in CAND unchanged. The golden tables (metadata.tsv, cases.txt, the CAS manifest,
                same-programs.txt) keep every BASE line in order; the coverage tables keep every
                BASE key at a count no smaller.
  C4 policy:    every constructor added or retired between BASE and CAND (read off wire-tags.json)
                is named in CAND's Test/fixtures/baseline/66ee4657-supplement-v1.policy.json.
                Reported, not refused unless --strict: the additions since the frozen baseline
                (Test/fixtures/baseline/66ee4657/families.json) that the policy does not name.
  C5 record:    `git diff --stat` of GENERATED_PATHS (the Makefile's list) between BASE and CAND.
"""
import json, os, re, shutil, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True).strip())
POLICY = 'Test/fixtures/baseline/66ee4657-supplement-v1.policy.json'
FROZEN = 'Test/fixtures/baseline/66ee4657/families.json'
WIRE_TAGS = 'tools/Effect4Gen/wire-tags.json'
GOLDEN_DIRS = ['ocaml/eff/goldens', 'ocaml/goldens/eff', 'ocaml/engine/cas/goldens']
VECTOR_EXT = ('.bin', '.json', '.ty', '.hex')
MANIFESTS = ['ocaml/eff/eff_manifest.txt', 'ocaml/goldens/eff/manifest.txt', 'ocaml/goldens/eff/wire-tags.txt']
VERDICTS = ['generated/corpus-index.tsv', 'ocaml/eff/goldens/corpus.txt', 'harness/truth/corpus-results.tsv']
ORDERED_TABLES = ['ocaml/eff/goldens/metadata.tsv', 'ocaml/engine/cas/goldens/cases.txt',
                  'ocaml/engine/cas/goldens/manifest.txt', 'ocaml/goldens/eff/same-programs.txt']
COUNT_TABLES = ['ocaml/eff/goldens/coverage.txt', 'ocaml/eff/goldens/coverage-metadata.txt']


def git(*args, binary=False):
    out = subprocess.run(['git', '-C', str(ROOT), *args], capture_output=True)
    if out.returncode != 0:
        return None
    return out.stdout if binary else out.stdout.decode('utf-8')


class Side:
    """One side of the comparison: a revision, the working tree (rev None), or a directory."""
    def __init__(self, rev=None, directory=None):
        self.rev, self.dir = rev, directory
        self.label = rev or (f'dir {directory}' if directory else 'working tree')

    def read(self, path, binary=False):
        if self.rev:
            return git('show', f'{self.rev}:{path}', binary=binary)
        p = (Path(self.dir) if self.dir else ROOT) / path
        if not p.is_file():
            return None
        return p.read_bytes() if binary else p.read_text(encoding='utf-8')

    def files(self, prefix):
        if self.rev:
            out = git('ls-tree', '-r', '--name-only', self.rev, '--', prefix)
            return [] if out is None else [l for l in out.splitlines() if l]
        base = (Path(self.dir) if self.dir else ROOT)
        top = base / prefix
        if not top.exists():
            return []
        return sorted(str(p.relative_to(base)) for p in top.rglob('*') if p.is_file())


def policy_of(side):
    text = side.read(POLICY)
    return json.loads(text) if text else {}


# ------------------------------------------------------------------ C1 goldens
def c1(base, cand, pol):
    migrations = set(pol.get('vector_migrations', [])) | set(pol.get('vector_removals', []))
    vectors = [f for d in GOLDEN_DIRS for f in base.files(d) if f.endswith(VECTOR_EXT)]
    # the frozen baselines are the per-commit directories; the policy file beside them is the one
    # file an append must change (C4 judges it, and its diff is the review event)
    vectors += [f for f in base.files('Test/fixtures/baseline') if f.count('/') >= 4]
    changed, removed, named = [], [], []
    for f in vectors:
        a, b = base.read(f, binary=True), cand.read(f, binary=True)
        key = f[len('ocaml/'):] if f.startswith('ocaml/') else f
        if b is None:
            (named if key in migrations else removed).append(f)
        elif a != b:
            (named if key in migrations else changed).append(f)
    added = [f for d in GOLDEN_DIRS for f in cand.files(d)
             if f.endswith(VECTOR_EXT) and base.read(f, binary=True) is None]
    ok = not changed and not removed
    print(f'C1 goldens: {"PASS" if ok else "REFUSE"}: {len(vectors)} byte vectors at BASE; '
          f'{len(changed)} changed, {len(removed)} removed, {len(named)} changed or removed by policy '
          f'name, {len(added)} added')
    for f in changed: print(f'  changed: {f}')
    for f in removed: print(f'  removed: {f}')
    for f in added[:20]: print(f'  added: {f}')
    return ok


# ------------------------------------------------------------------ C2 alphabets
def tags_of(side):
    text = side.read(WIRE_TAGS)
    return json.loads(text)['families'] if text else {}


def manifest_lines(text):
    """`Family: a b c` or `Lean.Name (oname) inductive: a b(c) …` → {family: [items]}."""
    out = {}
    for line in (text or '').splitlines():
        m = re.match(r'^(\S+)(?: \([^)]*\))?(?: (?:inductive|structure))?:\s*(.*)$', line)
        if m:
            depth, item, items = 0, '', []
            for ch in m.group(2).strip():
                if ch == ' ' and depth == 0:
                    if item: items.append(item)
                    item = ''
                    continue
                depth += (ch == '(') - (ch == ')')
                item += ch
            if item: items.append(item)
            out[m.group(1)] = items
    return out


def c2(base, cand, pol):
    problems = []
    tb, tc = tags_of(base), tags_of(cand)
    retirements = set(pol.get('constructor_retirements', []))
    for fam, rows in tb.items():
        crow = tc.get(fam)
        if crow is None:
            problems.append(f'wire-tags: family {fam} left the file'); continue
        for where in ('active', 'retired'):
            for name, tag in rows[where].items():
                act, ret = crow['active'].get(name), crow['retired'].get(name)
                if where == 'active' and act is None and ret == tag:
                    if f'{fam}.{name}' not in retirements:
                        problems.append(f'wire-tags: {fam}.{name} retired without a policy name')
                elif where == 'retired' and ret != tag:
                    problems.append(f'wire-tags: retired {fam}.{name}={tag} changed or removed')
                elif where == 'active' and act != tag:
                    problems.append(f'wire-tags: {fam}.{name}={tag} became {act if act is not None else ret}')
    for fam, rows in tc.items():
        used = list(rows['active'].values()) + list(rows['retired'].values())
        dup = sorted({t for t in used if used.count(t) > 1})
        if dup: problems.append(f'wire-tags: {fam} gives the tags {dup} twice')
        before = tb.get(fam)
        if before:
            old = set(before['active'].values()) | set(before['retired'].values())
            for name, tag in rows['active'].items():
                if name not in before['active'] and name not in before['retired'] and tag in old:
                    problems.append(f'wire-tags: new {fam}.{name} reuses tag {tag}')
    for path in MANIFESTS:
        mb, mc = manifest_lines(base.read(path)), manifest_lines(cand.read(path))
        for fam, items in mb.items():
            got = mc.get(fam)
            if got is None:
                problems.append(f'{path}: family {fam} left'); continue
            if got[:len(items)] != items:
                i = next(i for i, (x, y) in enumerate(zip(items, got + [None] * len(items))) if x != y)
                problems.append(f'{path}: {fam} position {i}: BASE {items[i]!r}, CAND {got[i] if i < len(got) else None!r}')
    ok = not problems
    appended = {fam: [n for n in tc[fam]['active'] if n not in tb.get(fam, {}).get('active', {})]
                for fam in tc}
    appended = {f: ns for f, ns in appended.items() if ns}
    print(f'C2 alphabets: {"PASS" if ok else "REFUSE"}: {len(tb)} tag families, {len(MANIFESTS)} manifests; '
          f'appended {sum(map(len, appended.values()))} constructors {appended if appended else ""}')
    for p in problems: print(f'  {p}')
    return ok


# ------------------------------------------------------------------ C3 verdicts
def rows(text):
    return [l for l in (text or '').splitlines() if l and not l.startswith('#')]


def keyed(text):
    out = {}
    for l in rows(text):
        k = l.split('\t')[0].split(' ')[0]
        out[k] = l
    return out


def c3(base, cand, pol):
    problems, judged = [], 0
    for path in VERDICTS:
        tb, tc = base.read(path), cand.read(path)
        if tb is None:
            print(f'  {path}: absent at BASE (not judged)'); continue
        kb, kc = keyed(tb), keyed(tc)
        judged += len(kb)
        for k, line in kb.items():
            if kc.get(k) != line:
                problems.append(f'{path}: {k}: BASE {line!r} CAND {kc.get(k)!r}')
    for path in ORDERED_TABLES:
        lb, lc = rows(base.read(path)), rows(cand.read(path))
        it = iter(lc)
        missing = [l for l in lb if not any(l == x for x in it)]
        if missing:
            problems.append(f'{path}: {len(missing)} BASE lines missing or out of order, first {missing[0]!r}')
    for path in COUNT_TABLES:
        kb, kc = keyed(base.read(path)), keyed(cand.read(path))
        for k, line in kb.items():
            n_b = int(line.split('\t')[-1]); got = kc.get(k)
            n_c = int(got.split('\t')[-1]) if got else -1
            if n_c < n_b:
                problems.append(f'{path}: {k}: count {n_b} became {n_c}')
    ok = not problems
    print(f'C3 verdicts: {"PASS" if ok else "REFUSE"}: {judged} verdict rows at BASE over {len(VERDICTS)} '
          f'lanes; {len(ORDERED_TABLES)} ordered and {len(COUNT_TABLES)} count tables')
    for p in problems[:20]: print(f'  {p}')
    return ok


# ------------------------------------------------------------------ C4 policy
def c4(base, cand, pol, strict):
    tb, tc = tags_of(base), tags_of(cand)
    named_add = set(pol.get('constructor_additions', []))
    named_ret = set(pol.get('constructor_retirements', []))
    added, retired = [], []
    for fam, rows_ in tc.items():
        before = tb.get(fam, {'active': {}, 'retired': {}})
        added += [f'{fam}.{n}' for n in rows_['active'] if n not in before['active'] and n not in before['retired']]
        retired += [f'{fam}.{n}' for n in rows_['retired'] if n not in before['retired']]
    unnamed = [c for c in added if c not in named_add] + [c for c in retired if c not in named_ret]
    frozen = json.loads(cand.read(FROZEN) or '{}')
    fams = frozen.get('families', frozen)
    pre = []
    if isinstance(fams, dict):
        items = fams.items()
    else:
        items = [(f.get('family'), f) for f in fams]
    for fam, desc in items:
        ctors = desc.get('constructors') if isinstance(desc, dict) else None
        if fam not in tc or ctors is None: continue
        old = {c if isinstance(c, str) else c.get('name') for c in ctors}
        for n in tc[fam]['active']:
            if n not in old and f'{fam}.{n}' not in named_add and f'{fam}.{n}' not in added:
                pre.append(f'{fam}.{n}')
    ok = not unnamed and (not strict or not pre)
    print(f'C4 policy: {"PASS" if ok else "REFUSE"}: {len(added)} added and {len(retired)} retired between '
          f'BASE and CAND; {len(unnamed)} not named in {POLICY}')
    for c in unnamed: print(f'  not named: {c}')
    print(f'  pre-existing (since the frozen baseline, not named; {"refused" if strict else "reported"}): '
          f'{len(pre)} {pre}')
    return ok


# ------------------------------------------------------------------ C5 record
def generated_paths():
    text = (ROOT / 'Makefile').read_text().replace('\\\n', ' ')
    defs = {m.group(1): m.group(2) for m in re.finditer(r'^([A-Z_]+)\s*:=\s*(.*)$', text, re.M)}
    def expand(s, depth=0):
        return re.sub(r'\$\(([A-Z_]+)\)', lambda m: expand(defs.get(m.group(1), ''), depth + 1), s) if depth < 5 else s
    return expand(defs['GENERATED_PATHS']).split()


def c5(base, cand):
    paths = generated_paths()
    if cand.dir:
        print('C5 record: (a directory candidate has no git diff)'); return
    args = ['diff', '--stat=120', base.rev] + ([cand.rev] if cand.rev else []) + ['--'] + paths
    out = git(*args) or ''
    lines = out.strip().splitlines()
    print(f'C5 record: git diff --stat over {len(paths)} GENERATED_PATHS entries: '
          f'{lines[-1].strip() if lines else "no change"}')
    for l in lines[:-1][:60]: print(f'  {l.strip()}')


def run(base, cand, strict=False):
    print(f'conservativity: BASE {base.label}, CAND {cand.label}')
    pol = policy_of(cand)
    results = [c1(base, cand, pol), c2(base, cand, pol), c3(base, cand, pol), c4(base, cand, pol, strict)]
    c5(base, cand)
    ok = all(results)
    print(f'conservativity: {"PASS" if ok else "REFUSE"} ({sum(results)} of 4 clauses pass)')
    return 0 if ok else 1


# ------------------------------------------------------------------ the controls
def self_test():
    here = Path(__file__).resolve().parents[1] / 'fixtures' / 'conservativity'
    cases = json.loads((here / 'mutations.json').read_text())
    head = git('rev-parse', 'HEAD').strip()
    needed = (GOLDEN_DIRS + ['Test/fixtures/baseline', WIRE_TAGS] + MANIFESTS + VERDICTS
              + ORDERED_TABLES + COUNT_TABLES)
    failures = 0
    for case in cases:
        with tempfile.TemporaryDirectory(dir=os.environ.get('TMPDIR')) as d:
            archive = subprocess.run(['git', '-C', str(ROOT), 'archive', head, '--', *needed], capture_output=True, check=True).stdout
            subprocess.run(['tar', '-x', '-C', d], input=archive, check=True)
            for m in case['edits']:
                p = Path(d) / m['path']
                if 'flip_last_byte' in m:
                    b = bytearray(p.read_bytes()); b[-1] ^= 1; p.write_bytes(bytes(b))
                else:
                    t = p.read_text(encoding='utf-8')
                    assert t.count(m['old']) == 1, (case['name'], m['path'], m['old'])
                    p.write_text(t.replace(m['old'], m['new']), encoding='utf-8')
            print(f'--- control {case["name"]} (expect {case["expect"]})')
            code = run(Side(rev=head), Side(directory=d))
            got = 'PASS' if code == 0 else 'REFUSE'
            want_clause = case.get('clause')
            status = 'ok' if got == case['expect'] else 'WRONG'
            if status == 'WRONG': failures += 1
            print(f'--- control {case["name"]}: {got} ({status}{", the clause " + want_clause if want_clause else ""})')
    print(f'self-test: {len(cases) - failures} of {len(cases)} controls as expected')
    return 0 if failures == 0 else 1


def main(argv):
    strict = '--strict' in argv
    argv = [a for a in argv if a != '--strict']
    if argv == ['--self-test']:
        return self_test()
    if len(argv) == 3 and argv[1] == '--cand-dir':
        return run(Side(rev=argv[0]), Side(directory=argv[2]), strict)
    if len(argv) in (1, 2):
        return run(Side(rev=argv[0]), Side(rev=argv[1] if len(argv) == 2 else None), strict)
    print(__doc__); return 2


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
