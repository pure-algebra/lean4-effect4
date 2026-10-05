"""Finite mirrors of committed name checks, not execution of Lean or OCaml."""
import hashlib, json, subprocess, sys
from pathlib import Path
ROOT = Path('/Users/pooks/Dev/lean4-effect4')
REV = '8b236fa7f31a67d22a472a3f87a918df215dce5f'
OUT = Path(__file__).parent
FILES = ['src/OCaml5/Lcnf/Builtins.lean', 'src/OCaml5/Lcnf/Translate.lean',
         'src/OCaml5/Lcnf/Externs.lean', 'src/OCaml5/Lcnf/Naming.lean',
         'src/OCaml5/Ml/Check.lean', 'src/OCaml5/Tools/LcnfGen.lean',
         'ocaml/engine/externs.txt', 'ocaml/engine/tools/api_engine_prelude.ml']
def at(path):
    return subprocess.check_output(['git', 'show', f'{REV}:{path}'], cwd=ROOT).decode()
src = {p: at(p) for p in FILES}
t = src['src/OCaml5/Lcnf/Translate.lean']
c = src['src/OCaml5/Ml/Check.lean']
b = src['src/OCaml5/Lcnf/Builtins.lean']
assert 'if reservedNames.contains name || translatorNames.contains name then' in t
assert '(Ml.shadowDiags guarded d.bind)' in t
assert 'e.values.contains n || guarded.contains n' in c
assert 'env.shadows b.name ps' in c
assert '| .fn ps b => env.shadows site ps ++ checkExpr (env.withValues ps)' in c
assert 'fn Effect4.Machine.RunMachine.finished 1 sh_machine_finished' in src['ocaml/engine/externs.txt']
assert 'let sh_machine_finished m =' in src['ocaml/engine/tools/api_engine_prelude.ml']
assert 'sh_machine_finished' not in b
# For this witness, only membership of these names matters. The full table is not reimplemented.
reserved = {'_b1','_b2','_b3','fst','snd','max_int','lcnf_nat_mul','lcnf_nat_pow',
            'lcnf_nat_shift_left','lcnf_list_contains','lcnf_utf8_bytes','lcnf_utf8_length',
            'min','max','not','failwith'}
checks = []
def check(name, observed, expected):
    assert observed == expected, (name,observed,expected)
    checks.append({'name': name, 'observed': observed, 'expected': expected, 'passed': True})
def emission_names(names):
    seen = set()
    for name in names:
        if name in seen: return [f'duplicate emitted name: {name}']
        if name in reserved: return [f'emitted name is reserved: {name}']
        seen.add(name)
    return []
def shadows(scope, guarded, batch):
    return [name for name in batch if name not in ('_', '()') and (name in scope or name in guarded)]
def leaf_binding_shadow(guarded, params):
    # These witnesses have bodies with no new binders; checkExpr adds no shadow diagnostic.
    return shadows([], guarded, params)
check('ordinary distinct global names accepted', emission_names(['ordinary','entry']), [])
check('duplicate emitted name refused', emission_names(['ordinary','ordinary']), ['duplicate emitted name: ordinary'])
check('builtin support global collision refused', emission_names(['lcnf_nat_mul']), ['emitted name is reserved: lcnf_nat_mul'])
check('extern head collision admitted by emission name checks', emission_names(['sh_machine_finished','entry']), [])
check('top-level name is not checked as a local binder', leaf_binding_shadow(['sh_machine_finished'], ['m']), [])
check('local capture of same extern head refused', leaf_binding_shadow(['sh_machine_finished'], ['sh_machine_finished']), ['sh_machine_finished'])
# A constructed translated caller contains both an ordinary call and the extern call.
# The ordinary call supplies an edge to the shadowing declaration, forcing it before the caller.
# The named helper from the real prelude is true on an empty fiber table.
hand = lambda machine: all(f.get('exit') is not None for f in machine['fibers'])
generated = lambda machine: False
empty = {'fibers': []}
expected_pair = [generated(empty), hand(empty)]
env = {'sh_machine_finished': hand}
env['sh_machine_finished'] = generated
actual_pair = [env['sh_machine_finished'](empty), env['sh_machine_finished'](empty)]
check('constructed wrong global resolution witness', [expected_pair, actual_pair], [[False, True],[False, False]])
check('renamed generated declaration positive', [generated(empty), hand(empty)], [False,True])
check('distinct parameter batch accepted', leaf_binding_shadow([], ['x','y']), [])
check('repeated parameter batch missed', leaf_binding_shadow([], ['x','x']), [])
check('nested parameter still catches shadow', shadows(['x'], [], ['x']), ['x'])
check('wildcard repetitions bind nothing', leaf_binding_shadow([], ['_','_','()']), [])
# A scan over committed closure names, not raw OCaml parsing, bounds actual current impact.
extern_heads = {line.split()[3] for line in src['ocaml/engine/externs.txt'].splitlines()
                if line.startswith(('fn ', 'fn? ', 'ops ')) and '.' not in line.split()[3]}
manifest='ocaml/gen/closure-api_engine.tsv'
rows=at(manifest).splitlines()
header=rows[0].split('\t'); col=header.index('ocaml')
names={line.split('\t')[col] for line in rows[1:] if line}
collisions=sorted(names & extern_heads)
check('committed engine closure has no extern head collision', collisions, [])
result={'revision':REV,'python':sys.version,'kind':'Finite Python source mirrors; no Lean/OCaml execution or persisted-LCNF witness',
        'source_hashes':{p:hashlib.sha256(s.encode()).hexdigest() for p,s in src.items()},
        'checks':checks,'passed':len(checks),'actual_engine_extern_head_collisions':collisions,
        'scope':'The scalar name checks and sequential name-resolution example only. No complete checker, translator, compiler, or runtime simulation.'}
(OUT/'probe-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':len(checks),'committed_engine_extern_head_collisions':collisions,'revision':REV}))
