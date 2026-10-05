"""Source sites for seat T3b's design note (phase 1), at 5949fe4b.

Every tracked source line, outside a comment, that names
  (a) one of the eight read-modify-write `NativeOp` constructors with its function argument
      (`refUpdate f`, `(.refUpdate .incr)`), not the three-field `SyncOp` rows;
  (b) the function-name alphabet: `FnName`, one of its five constructors as a dotted literal,
      the four interpretations, T2's four lowerings and agreements;
  (c) the faces' name vocabulary: `fnSpelling`, `fnNames`, `lambdaShape`, `lambdaAtom`, `atom?`;
grouped by file and by the declaration the line sits in. Run from the worktree root:
`python3 docs/research/2026-10-04-seat-T3b/sites.py`.
"""
import re, subprocess, collections

ROWS = ['refUpdate', 'refGetAndUpdate', 'refUpdateAndGet', 'refUpdateSome', 'refGetAndUpdateSome',
        'refUpdateSomeAndGet', 'refModify', 'refModifySome']
NAMES = ['incr', 'double', 'zeroWhenPositive', 'noChange', 'takeAndBump']
row_alt = '|'.join(sorted(ROWS, key=len, reverse=True))
# a NativeOp row with one argument: `refUpdate f`, `.refUpdate .incr`, `(.refUpdate f)`,
# `NativeOp.refUpdate x`; a SyncOp row carries three (`SyncOp.refUpdate cell f env`)
native_row = re.compile(r'(?<![A-Za-z_.])(?:NativeOp\.|\.)?(' + row_alt + r')\b(?![_A-Za-z])')
syncop_row = re.compile(r'SyncOp\.(' + row_alt + r')\b')
fn_alpha = re.compile(r'\bFnName\b|\.(?:' + '|'.join(NAMES) + r')\b(?![_A-Za-z])|'
                      r'\b(?:updateTerm|updateSomeTerm|modifyTerm|modifySomeTerm)\b|'
                      r'\bFnName\.(?:total|partialUpdate|modify|modifySome)\b')
faces = re.compile(r'\bfnSpelling\b|\bfnNames\b|\blambdaShape\b|\blambdaAtom\b|\batom\?')
decl = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|public\s+)*'
                  r'(theorem|def|abbrev|instance|example|lemma|structure|inductive|proof_goal)\s+([^\s:(]*)')

def arity(code, at):
    """How many argument tokens follow a constructor name before a delimiter."""
    rest = re.split(r'=>|:=|[),\]|}]|\bwith\b|\bthen\b|\belse\b|\bfun\b', code[at:], maxsplit=1)[0]
    return len(rest.split())

def strip_comments(lines):
    """Drop `--` line comments and `/- … -/` blocks (docstrings included)."""
    depth = 0
    for line in lines:
        out, i = '', 0
        while i < len(line):
            if depth == 0 and line.startswith('--', i):
                break
            if line.startswith('/-', i):
                depth += 1; i += 2; continue
            if depth > 0 and line.startswith('-/', i):
                depth -= 1; i += 2; continue
            if depth == 0:
                out += line[i]
            i += 1
        yield out

files = subprocess.run(['git', 'ls-files', '*.lean'], capture_output=True, text=True).stdout.split()
per = collections.OrderedDict()
for f in files:
    if f.startswith('docs/'):
        continue
    raw = open(f, encoding='utf-8').read().splitlines()
    code = list(strip_comments(raw))
    cur = None
    hits = []
    for i, (line, c) in enumerate(zip(raw, code), 1):
        m = decl.match(line)
        if m:
            cur = m.group(2) or m.group(1)
        kinds = []
        if any(arity(c, m.end()) <= 1 for m in native_row.finditer(syncop_row.sub('', c))):
            # a `SyncOp` row carries three fields (`cell f env`); a `NativeOp` row one or none
            kinds.append('row')
        if fn_alpha.search(c):
            kinds.append('fn')
        if faces.search(c):
            kinds.append('face')
        if kinds:
            hits.append((i, cur, '+'.join(kinds)))
    if hits:
        per[f] = hits

total_lines = 0
decls = set()
by_kind = collections.Counter()
for f, hits in per.items():
    ds = sorted({h[1] or '?' for h in hits})
    decls |= {(f, d) for d in ds}
    total_lines += len(hits)
    for h in hits:
        for k in h[2].split('+'):
            by_kind[k] += 1
    kinds = collections.Counter(k for h in hits for k in h[2].split('+'))
    print(f"{f}: {len(hits)} lines ({', '.join(f'{k} {n}' for k, n in sorted(kinds.items()))}), "
          f"{len(ds)} declarations: {', '.join(ds)}")
print(f"files {len(per)}, declarations {len(decls)}, lines {total_lines}; "
      f"by kind: {dict(sorted(by_kind.items()))}")
src = [f for f in per if f.startswith('src/')]
tst = [f for f in per if f.startswith('Test/')]
tools = [f for f in per if f.startswith('tools/')]
print(f"src files {len(src)}, Test files {len(tst)}, tools files {len(tools)}")
