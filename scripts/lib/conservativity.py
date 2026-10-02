#!/usr/bin/env python3
"""Conservativity of an alphabet append (DI-47, R3.8; decisions row 172), as one command.

    scripts/check-conservativity.sh BASE [CAND] [--strict]   CAND a revision; omitted: the working tree
    scripts/check-conservativity.sh BASE --cand-dir DIR      the candidate's files read from DIR
    scripts/check-conservativity.sh --self-test              the controls (Test/fixtures/conservativity)

Probe Q's check (`docs/research/2026-10-01-type-language-probe/Q/bin/conservativity.py`), landed
by seat W2 with the repair decisions row 172 asks for (Codex, 20:46): every supplied revision is
resolved to a commit before anything is read (`git rev-parse --verify <rev>^{commit}`), refused by
name when it does not resolve, and a failed git command is a refusal, never an empty answer. A file
genuinely absent at a resolved revision stays a legitimate "absent" (a path added since BASE is
what the policy clause judges), distinct from an unreadable revision.

Properties. Reads committed files only (git blobs at resolved commits, or the candidate's files);
runs no producer and no build: it is the check that follows the producers of an append commit
and `make corpus`, so the inputs it judges are the regenerated groups. Each clause prints PASS or
REFUSE with the paths and names it judged. Exit 0 only when every clause passes; 1 on a refusal,
an unresolved revision or a failed git command (with the message); 2 on a usage error.

  C1 goldens:   every byte vector at BASE (`.bin .json .ty .hex` under the golden directories,
                and every file of the Test/fixtures/baseline/<commit>/ directories) is byte-identical
                in CAND, unless CAND's policy names it (vector_migrations / vector_removals); new
                vectors are listed as additions.
  C2 alphabets: tools/Effect4Gen/wire-tags.json: every BASE row (active or retired) keeps its tag;
                a tag is never given twice; an active row may leave only into `retired`, under a
                policy name. A key repeated inside one JSON object is refused (decisions row 174:
                `json.loads`, like Lean's `Json.parse`, keeps the last, so this loader refuses it).
                The generated manifests (ocaml/eff/eff_manifest.txt, ocaml/goldens/eff/manifest.txt,
                ocaml/goldens/eff/wire-tags.txt): each BASE family line is a prefix of CAND's
                (names and argument shapes), so an existing constructor is neither moved nor re-typed.
  C3 verdicts:  generated/corpus-index.tsv (Lean's wellTyped/readable verdict per program),
                ocaml/eff/goldens/corpus.txt (the golden programs' typing verdicts),
                harness/truth/corpus-results.tsv (the host lane, as committed): every BASE row is in
                CAND unchanged. The golden tables (metadata.tsv, cases.txt, the CAS manifest,
                same-programs.txt) keep every BASE line in order; the coverage tables keep every BASE
                key at a count no smaller.
  C4 policy:    every constructor added or retired between BASE and CAND (read off wire-tags.json)
                is named in CAND's Test/fixtures/baseline/66ee4657-supplement-v1.policy.json.
                Reported, refused only with --strict: the additions since the frozen baseline
                (Test/fixtures/baseline/66ee4657/families.json) the policy does not name. --strict
                waits for the owner's word on promoting refOf, deferredOf, var and unknown (row 172).
  C5 record:    `git diff --stat` of GENERATED_PATHS (the Makefile's list) between BASE and CAND.

The controls (`--self-test`): the ten of probe Q, each a mutation of a scratch extract of HEAD
judged against HEAD (R1-R9 refuse on the clause they name, G1 the wave appended and named passes),
and six on the revisions themselves, each run as this command: an invalid BASE, an invalid CAND
and both invalid, each with and without --strict, all refused with exit 1 and the message naming
the revision.
"""
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

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
MUTATIONS = 'Test/fixtures/conservativity/mutations.json'


class Refusal(Exception):
    """A refusal that stops the check before any clause: an unresolved revision, a failed git
    command, a repository that is not one. Exit 1, with the message."""


def repository_root():
    out = subprocess.run(['git', 'rev-parse', '--show-toplevel'], capture_output=True, text=True)
    if out.returncode != 0:
        raise Refusal('conservativity: REFUSE: not inside a git work tree '
                      f'(git rev-parse --show-toplevel: {out.stderr.strip()})')
    return Path(out.stdout.strip())


ROOT = None


def git(*args, binary=False):
    """One git command at the repository root; a non-zero exit is a refusal naming the command,
    never an empty answer (the defect Codex found at 20:46: a failed read read as absent data)."""
    out = subprocess.run(['git', '-C', str(ROOT), *args], capture_output=True)
    if out.returncode != 0:
        raise Refusal(f'conservativity: REFUSE: git {" ".join(args)} failed (exit {out.returncode}): '
                      f'{out.stderr.decode("utf-8", "replace").strip()}')
    return out.stdout if binary else out.stdout.decode('utf-8')


class Blobs:
    """Blobs at resolved commits through one `git cat-file --batch` process (one subprocess per
    check rather than one per file). A path is asked for only after the commit's listing shows
    it, so `missing` or a dead process is a refusal, never an absent file."""
    def __init__(self):
        self.proc = None

    def read(self, rev, path):
        if self.proc is None:
            self.proc = subprocess.Popen(['git', '-C', str(ROOT), 'cat-file', '--batch'],
                                         stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        spec = f'{rev}:{path}'
        self.proc.stdin.write(spec.encode('utf-8') + b'\n')
        self.proc.stdin.flush()
        header = self.proc.stdout.readline()
        parts = header.split()
        if len(parts) != 3 or parts[1] != b'blob':
            raise Refusal(f'conservativity: REFUSE: git cat-file --batch could not read {spec} '
                          f'(answered {header.decode("utf-8", "replace").strip() or "nothing"})')
        data = self.proc.stdout.read(int(parts[2]))
        self.proc.stdout.read(1)
        return data


BLOBS = Blobs()


def resolve(revisions):
    """Each supplied revision as a commit id, or a refusal naming every one that does not
    resolve (`git rev-parse --verify <rev>^{commit}`)."""
    resolved, bad = {}, []
    for role, rev in revisions:
        out = subprocess.run(['git', '-C', str(ROOT), 'rev-parse', '--verify', '--quiet', f'{rev}^{{commit}}'],
                             capture_output=True, text=True)
        if out.returncode != 0 or not out.stdout.strip():
            bad.append(f'the {role} revision {rev!r}')
        else:
            resolved[role] = out.stdout.strip()
    if bad:
        raise Refusal('conservativity: REFUSE: ' + ' and '.join(bad) +
                      (' does not' if len(bad) == 1 else ' do not') +
                      ' resolve to a commit (git rev-parse --verify <rev>^{commit}); nothing was compared')
    return resolved


class Side:
    """One side of the comparison: a resolved commit, the working tree (rev None), or a directory."""
    def __init__(self, rev=None, directory=None, label=None):
        self.rev, self.dir = rev, directory
        self.label = label or rev or (f'dir {directory}' if directory else 'working tree')
        self._listing = None

    def listing(self):
        """Every file path at the commit, read once: a path not in it is genuinely absent there."""
        if self._listing is None:
            self._listing = set(git('ls-tree', '-r', '--name-only', self.rev).splitlines())
        return self._listing

    def read(self, path, binary=False):
        if self.rev:
            if path not in self.listing():
                return None
            data = BLOBS.read(self.rev, path)
            return data if binary else data.decode('utf-8')
        p = (Path(self.dir) if self.dir else ROOT) / path
        if not p.is_file():
            return None
        return p.read_bytes() if binary else p.read_text(encoding='utf-8')

    def files(self, prefix):
        if self.rev:
            top = prefix.rstrip('/') + '/'
            return sorted(f for f in self.listing() if f.startswith(top) or f == prefix)
        base = (Path(self.dir) if self.dir else ROOT)
        top = base / prefix
        if not top.exists():
            return []
        return sorted(str(p.relative_to(base)) for p in top.rglob('*') if p.is_file())


class RepeatedKey(ValueError):
    pass


def load_json_strict(text):
    """`json.loads` refusing a key given twice inside one object (decisions row 174): the plain
    loader keeps the last, which hides a repeated tag row."""
    def hook(pairs):
        keys = [k for k, _ in pairs]
        dup = sorted({k for k in keys if keys.count(k) > 1})
        if dup:
            raise RepeatedKey(f'the key(s) {dup} given twice in one object')
        return dict(pairs)
    return json.loads(text, object_pairs_hook=hook)


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
    """The families of wire-tags.json, read strictly; a repeated key is reported by C2."""
    text = side.read(WIRE_TAGS)
    if not text:
        return {}, None
    try:
        return load_json_strict(text)['families'], None
    except RepeatedKey as error:
        return json.loads(text)['families'], str(error)


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
    tb, _ = tags_of(base)
    tc, repeated = tags_of(cand)
    if repeated:
        problems.append(f'wire-tags: {repeated} (the loaders refuse it, decisions row 174)')
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
    tb, _ = tags_of(base)
    tc, _ = tags_of(cand)
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
    out = git('diff', '--stat=120', base.rev, *([cand.rev] if cand.rev else []), '--', *paths)
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
    cases = json.loads((ROOT / MUTATIONS).read_text())
    head = resolve([('HEAD', 'HEAD')])['HEAD']
    needed = (GOLDEN_DIRS + ['Test/fixtures/baseline', WIRE_TAGS] + MANIFESTS + VERDICTS
              + ORDERED_TABLES + COUNT_TABLES)
    at_head = Side(rev=head)
    present = [p for p in needed if p in at_head.listing() or at_head.files(p)]
    failures, total = 0, 0
    for case in cases:
        total += 1
        with tempfile.TemporaryDirectory(dir=os.environ.get('TMPDIR')) as d:
            archive = git('archive', head, '--', *present, binary=True)
            subprocess.run(['tar', '-x', '-C', d], input=archive, check=True)
            for m in case['edits']:
                p = Path(d) / m['path']
                if 'flip_last_byte' in m:
                    b = bytearray(p.read_bytes()); b[-1] ^= 1; p.write_bytes(bytes(b))
                else:
                    t = p.read_text(encoding='utf-8')
                    if t.count(m['old']) != 1:
                        raise Refusal(f'self-test: {case["name"]}: the anchor {m["old"]!r} is not '
                                      f'exactly once in {m["path"]} at HEAD; repair the fixture')
                    p.write_text(t.replace(m['old'], m['new']), encoding='utf-8')
            print(f'--- control {case["name"]} (expect {case["expect"]})')
            code = run(Side(rev=head, label=f'HEAD {head[:8]}'), Side(directory=d))
            got = 'PASS' if code == 0 else 'REFUSE'
            want_clause = case.get('clause')
            status = 'ok' if got == case['expect'] else 'WRONG'
            if status == 'WRONG': failures += 1
            print(f'--- control {case["name"]}: {got} ({status}{", the clause " + want_clause if want_clause else ""})')
    # the revisions themselves (decisions row 172 amended; Codex 20:46): run as the command, so the
    # exit code and the message are the ones a caller sees
    me = [sys.executable, str(Path(__file__).resolve())]
    bad_base, bad_cand = 'no-such-conservativity-base', 'no-such-conservativity-candidate'
    revision_cases = [
        ('V1 invalid BASE', [bad_base, head], [bad_base]),
        ('V2 invalid CAND', [head, bad_cand], [bad_cand]),
        ('V3 invalid BASE and CAND', [bad_base, bad_cand], [bad_base, bad_cand]),
    ]
    for name, args, names in revision_cases:
        for strict in (False, True):
            total += 1
            argv = args + (['--strict'] if strict else [])
            label = name + (' --strict' if strict else '')
            r = subprocess.run(me + argv, cwd=ROOT, capture_output=True, text=True)
            text = r.stdout + r.stderr
            refused = r.returncode == 1 and ('does not resolve to a commit' in text
                                              or 'do not resolve to a commit' in text)
            ok = refused and all(repr(n) in text for n in names) and 'PASS' not in text
            if not ok: failures += 1
            print(f'--- control {label}: exit {r.returncode} ({"ok" if ok else "WRONG"}): '
                  f'{text.strip().splitlines()[-1] if text.strip() else "(no output)"}')
    print(f'self-test: {total - failures} of {total} controls as expected')
    return 0 if failures == 0 else 1


def main(argv):
    global ROOT
    ROOT = repository_root()
    strict = '--strict' in argv
    argv = [a for a in argv if a != '--strict']
    if argv == ['--self-test']:
        return self_test()
    if len(argv) == 3 and argv[1] == '--cand-dir':
        if not Path(argv[2]).is_dir():
            raise Refusal(f'conservativity: REFUSE: the candidate directory {argv[2]!r} does not exist')
        base = resolve([('BASE', argv[0])])
        return run(Side(rev=base['BASE'], label=f'{argv[0]} ({base["BASE"][:8]})'),
                   Side(directory=argv[2]), strict)
    if len(argv) in (1, 2):
        revs = [('BASE', argv[0])] + ([('CAND', argv[1])] if len(argv) == 2 else [])
        got = resolve(revs)
        base = Side(rev=got['BASE'], label=f'{argv[0]} ({got["BASE"][:8]})')
        cand = (Side(rev=got['CAND'], label=f'{argv[1]} ({got["CAND"][:8]})') if len(argv) == 2
                else Side())
        return run(base, cand, strict)
    print(__doc__)
    return 2


if __name__ == '__main__':
    try:
        sys.exit(main(sys.argv[1:]))
    except Refusal as error:
        print(error)
        sys.exit(1)
