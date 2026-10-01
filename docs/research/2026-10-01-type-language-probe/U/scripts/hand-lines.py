#!/usr/bin/env python3
"""Probe U, questions 2 and 3: the hand lines of every traversal the generic families replace,
measured in the tree (non-blank, non-comment lines from the definition's first line to the next
top-level command; OCaml by the line range named, comments dropped).

    python3 U/scripts/hand-lines.py            (from the worktree root; prints a table and totals)
"""
import os, re, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..', '..'))
TOP = re.compile(r'^(theorem|def|private|protected|lemma|instance|abbrev|structure|inductive|@\[|/--|/-!|#|end |namespace|section|open|set_option|example|noncomputable|mutual|attribute|variable|partial|fold_of|deriving)')

LEAN = [
    ('c', 'src/Effect4/Program/Ty.lean', r'^def renderRaw\b'),
    ('c', 'src/Effect4/Schema/Bridge.lean', r'^def schema\b'),
    ('c', 'src/Effect4/Program/Ty.lean', r'^def key\b'),
    ('b', 'src/Effect4/Laws/Program/Template.lean', r'^def varsOf\b'),
    ('b', 'src/Effect4/Program/Ty.lean', r'^def closed\b'),
    ('b', 'src/Effect4/Laws/Program/Template.lean', r'^def templateAdmissible\b'),
    ('b', 'src/Effect4/Schema/Codec.lean', r'^def isSupported\b'),
    ('b', 'src/Effect4/Laws/Program/Typed/Membership.lean', r'^def handleFreeAlg\b'),
    ('b', 'src/Effect4/Laws/Program/TypeAlgebra.lean', r'^def valueVarsAlg\b'),
    ('b', 'src/Effect4/Program/Admission.lean', r'^def findInt\b'),
    ('b', 'src/Effect4/Program/Admission.lean', r'^def internalHandleScan\b'),
    ('b2', 'src/Effect4/Program/Ty.lean', r'^def members\b'),
    ('b2', 'src/Effect4/Program/Eff.lean', r'^def isTagTy\b'),
    ('b2', 'src/Effect4/Program/Eff.lean', r'^def rawSupportedErrTy\b'),
    ('b2', 'src/Effect4/Program/NativeAtom.lean', r'^def projectProduct\b'),
    ("c'", 'tools/Tools/ProfileJson.lean', r'^def tyJson\b'),
    ("c'", 'src/OCaml5/Eff/Goldens.lean', r'^def tyV\b'),
    ("c'", 'src/OCaml5/Eff/Emit.lean', r'^def tyO\b'),
    ("c'", 'tools/Conform/Effect4/LcnfMl.lean', r'^def tyT\b'),
    ("c'", 'tools/Conform/Effect4/LcnfMl.lean', r'^def tyOcaml\b'),
    ("c'", 'tools/Conform/Effect4/LcnfSemantics.lean', r'^def tyValue\b'),
    ("c'", 'tools/Conform/Effect4/LcnfSemantics.lean', r'^partial def valueTy\?'),
]
OCAML = [
    ("c'", 'ocaml/engine/e4_program.ml', 'of_ty', 130, 154),
    ("c''", 'ocaml/eff/test/prop_wire.ml', 'rand_ty', 155, 171),
]

def lean_span(path, pat):
    L = open(os.path.join(ROOT, path)).read().split('\n')
    for i, l in enumerate(L):
        if re.match(pat, l):
            j = i + 1
            while j < len(L) and not TOP.match(L[j]):
                j += 1
            body = [x for x in L[i:j] if x.strip() and not x.strip().startswith('--')]
            return i + 1, j, len(body)
    sys.exit(f'not found: {path} {pat}')

def ocaml_span(path, a, b):
    L = open(os.path.join(ROOT, path)).read().split('\n')[a - 1:b]
    n, incomment = 0, False
    for x in L:
        s = x.strip()
        if incomment:
            if '*)' in s:
                incomment = False
            continue
        if s.startswith('(*'):
            incomment = '*)' not in s
            continue
        if s:
            n += 1
    return n

tot = {}
print('family\tsite\tlines')
for fam, path, pat in LEAN:
    a, b, n = lean_span(path, pat)
    name = pat.split('def ')[-1].rstrip('\\b').replace('\\?', '?')
    print(f'{fam}\t{path}:{a}\t{name}\t{n}')
    tot[fam] = tot.get(fam, 0) + n
lean_total = sum(tot.values())
for fam, path, name, a, b in OCAML:
    n = ocaml_span(path, a, b)
    print(f'{fam}\t{path}:{a}-{b}\t{name}\t{n}')
    tot['ocaml'] = tot.get('ocaml', 0) + n
print('Lean traversals:', len(LEAN), '| hand lines:', lean_total, '|',
      ', '.join(f'{k} {v}' for k, v in tot.items() if k != 'ocaml'))
print('OCaml mirrors: 2 | hand lines:', tot['ocaml'])
