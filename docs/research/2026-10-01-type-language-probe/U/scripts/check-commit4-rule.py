#!/usr/bin/env python3
"""Probe U: the commit-4 rule as a check a reviewer runs.

    python3 U/scripts/check-commit4-rule.py <census.log> [<census-mirrors.log>]

The rule: no hand case analysis on `Ty` outside the generated folds and
`Laws/Program/Typed/Membership.lean`. Read from the tree's own instruments
(`#traversal_census Effect4.Program.Ty` and `#exhaustive_gate Effect4.Program.Ty`, plus the same
two `under OCaml5`, `under Tools`, `under Conform`):

  R1  no `structural` or `wf` row: every recursive traversal is a `fold` (through `cata_ty` and a
      named algebra) or `generated` (a module tools/Effect4Gen/manifest.json writes);
  R2  a `one-level` row only in a generated module or in Membership.lean;
  R3  an exhaustive-gate row (a compiled `match` reading `Ty`) only in a generated module or in
      Membership.lean — so no hand catch-all decides a new constructor's class anywhere else;
  R4  the mirror modules (OCaml5, Tools, Conform) have no `structural` row: the reflections are
      emitted from the signature.

Exempt by name (each with its reason in the note, §6.2): the derived `Repr` instance until the
generator emits it for the nested `Ty`; and two pass-through matchers, where a `match` on another
type carries the `Ty` as a discriminant bound to a variable in every arm, so the gate lists it
although nothing is cased (`selectRefusal.match_1`, `Decision.arms.match_4`; the instrument does
not say whether every arm binds the discriminant, so these are named). Prints every violation and
exits 1 when there is one; on today's tree it is the red baseline (the distance from the rule).
"""
import sys

GENERATED_MODULES = {
    'Effect4.Program.Fold', 'Effect4.Laws.Program.TyView', 'Effect4.Store.Domain.Derived.Program',
    # the modules the wave would add (the patched generator's output):
    'Effect4.Program.TyFoldExtras', 'Effect4.Program.TyTables',
}
ALLOWED_MODULES = {'Effect4.Laws.Program.Typed.Membership'}
EXEMPT = {'Effect4.Program.instReprTy.repr'}
# Pass-through matchers: the `Ty` discriminant is a variable in every arm (no case analysis).
PASS_THROUGH = {'Effect4.Program.selectRefusal.match_1', 'Effect4.Program.Decision.arms.match_4'}

def parse(path):
    census, gate, mode = [], [], None
    for line in open(path).read().splitlines():
        if line.startswith('#traversal_census'):
            mode = 'c'; continue
        if line.startswith('#exhaustive_gate'):
            mode = 'g'; continue
        if line.startswith('==='):
            mode = None; continue
        if not line.startswith('  '):
            continue
        p = line.strip().split('\t')
        if mode == 'c':
            cls, loc, name = p[0], p[1], p[2].split(' [')[0]
            census.append((cls, loc.rsplit(':', 1)[0], name))
        elif mode == 'g':
            gate.append((p[0].split(' [')[0], p[1], p[2], p[5]))
    return census, gate

def main():
    census, gate = parse(sys.argv[1])
    v = []
    for cls, mod, name in census:
        if name in EXEMPT or mod in ALLOWED_MODULES:
            continue
        if cls in ('structural', 'wf'):
            v.append(f'R1 {cls:10} {name} ({mod})')
        if cls == 'one-level' and mod not in GENERATED_MODULES:
            v.append(f'R2 one-level  {name} ({mod})')
    for name, mod, matcher, ca in gate:
        if name.endswith('.hom') or name in EXEMPT or matcher in PASS_THROUGH or mod in ALLOWED_MODULES or mod in GENERATED_MODULES:
            continue
        v.append(f'R3 {ca:14} {name} ({mod}, {matcher})')
    seen = set()
    for path in sys.argv[2:]:
        mc, _ = parse(path)
        for cls, mod, name in mc:
            if cls == 'structural' and name not in seen:
                seen.add(name)
                v.append(f'R4 structural {name} ({mod})')
    for x in v:
        print(x)
    rules = {}
    for x in v:
        rules[x[:2]] = rules.get(x[:2], 0) + 1
    print(f'{len(v)} violation(s): ' + ', '.join(f'{k} {rules[k]}' for k in sorted(rules)))
    sys.exit(1 if v else 0)

if __name__ == '__main__':
    main()
