#!/usr/bin/env python3
"""Probe U, question 4: the two hand OCaml mirrors of `Ty`, emitted from the family description.

    python3 U/scripts/emit-ocaml-ty.py <eff_manifest.txt> <e4_program.ml> <prop_wire.ml> <outdir>

Input: the `Effect4.Program.Ty (ty) inductive:` line of `ocaml/eff/eff_manifest.txt` — the family
description EffGen already writes from the Lean declaration (constructor names in declaration
order, each argument's OCaml carrier). Output, into <outdir>, the two files with their hand blocks
replaced by emitted ones:

* `e4_program.ml`: `of_ty` (Eff_types.ty -> A.ty, the identity algebra between two generated
  declarations of one signature) and the constructor-count pin, both from the manifest line;
* `prop_wire.ml`: `rand_ty`, the random generator, reaching every constructor (the hand one
  reaches 15 of 20 and ends `| _ -> Ty_union`, which no exhaustiveness check can see).

Everything else in the two files is copied byte for byte; the script refuses if a hand block is
not where it expects it (so a drifted file is a refusal, not a silent splice).
"""
import re, sys, os

def read_family(manifest, oname='ty'):
    for line in open(manifest):
        m = re.match(r'^(\S+) \((\w+)\) inductive: (.*)$', line.rstrip('\n'))
        if m and m.group(2) == oname:
            items, depth, cur = [], 0, ''
            for ch in m.group(3):
                if ch == '(':
                    depth += 1
                elif ch == ')':
                    depth -= 1
                if ch == ' ' and depth == 0:
                    if cur: items.append(cur)
                    cur = ''
                else:
                    cur += ch
            if cur: items.append(cur)
            ctors = []
            for it in items:
                mm = re.match(r'^(\w+)(?:\((.*)\))?$', it)
                args = [a.strip() for a in mm.group(2).split(',')] if mm.group(2) else []
                ctors.append((mm.group(1), args))
            return ctors
    raise SystemExit(f'{manifest}: no inductive line for ({oname})')

def ctor(c): return 'Ty_' + c

def paren(e): return '(' + e + ')' if ' ' in e else e

def emit_of_ty(ctors):
    out = ['  let rec of_ty : Eff_types.ty -> A.ty = function']
    for c, args in ctors:
        if not args:
            out.append(f'    | Eff_types.{ctor(c)} -> A.{ctor(c)}')
            continue
        vs = [f'a{i}' for i in range(len(args))]
        conv = [f'of_ty {v}' if a == 'ty' else v for v, a in zip(vs, args)]
        lhs = vs[0] if len(vs) == 1 else '(' + ', '.join(vs) + ')'
        rhs = paren(conv[0]) if len(conv) == 1 else '(' + ', '.join(conv) + ')'
        out.append(f'    | Eff_types.{ctor(c)} {lhs} -> A.{ctor(c)} {rhs}')
    return '\n'.join(out) + '\n'

def emit_rand_ty(ctors):
    leaves = [(c, a) for c, a in ctors if 'ty' not in a]
    gen = {'ty': 'rand_ty (d - 1)', 'string': 'rand_string ()', 'int': 'rand_nat ()'}
    def build(c, args):
        if not args: return ctor(c)
        xs = [gen[a] for a in args]
        return f'{ctor(c)} ' + (paren(xs[0]) if len(xs) == 1 else '(' + ', '.join(xs) + ')')
    out = ['(* GENERATED from the Ty line of eff_manifest.txt (probe U): every constructor, the',
           '   leaves alone at depth 0. *)',
           'let rec rand_ty d =',
           f'  if d <= 0 then',
           f'    match ri {len(leaves)} with']
    for i, (c, a) in enumerate(leaves):
        pat = str(i) if i < len(leaves) - 1 else '_'
        out.append(f'    | {pat} -> {build(c, a)}')
    out.append(f'  else')
    out.append(f'    match ri {len(ctors)} with')
    for i, (c, a) in enumerate(ctors):
        pat = str(i) if i < len(ctors) - 1 else '_'
        out.append(f'    | {pat} -> {build(c, a)}')
    return '\n'.join(out) + '\n'

def splice(text, start_pat, end_pat, new, what):
    s = text.find(start_pat)
    if s < 0: raise SystemExit(f'{what}: start {start_pat!r} not found')
    e = text.find(end_pat, s)
    if e < 0: raise SystemExit(f'{what}: end {end_pat!r} not found')
    return text[:s] + new + text[e:]

def main():
    manifest, e4, prop, outdir = sys.argv[1:5]
    ctors = read_family(manifest)
    t = open(e4).read()
    t = t.replace('let () = assert (List.length Eff_types.ctor_names_ty = 20)',
                  f'let () = assert (List.length Eff_types.ctor_names_ty = {len(ctors)})  (* emitted *)')
    t = splice(t, '  let rec of_ty : Eff_types.ty -> A.ty = function', '\n  let of_lit', emit_of_ty(ctors), 'e4_program.ml of_ty')
    os.makedirs(outdir, exist_ok=True)
    open(os.path.join(outdir, 'e4_program.ml'), 'w').write(t)
    p = open(prop).read()
    p = splice(p, 'let rec rand_ty d =', '\nlet rand_key', emit_rand_ty(ctors), 'prop_wire.ml rand_ty')
    open(os.path.join(outdir, 'prop_wire.ml'), 'w').write(p)
    print(f'{len(ctors)} constructors read from {manifest}; '
          f'{sum(1 for c, a in ctors if "ty" not in a)} leaves; wrote e4_program.ml and prop_wire.ml to {outdir}')

if __name__ == '__main__':
    main()
