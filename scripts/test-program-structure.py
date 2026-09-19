#!/usr/bin/env python3
"""Independent failures for the selected engine shape reader; no Lean or generated edits."""
import copy
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent/'lib'))
from program_structure import selected_view, declarations

family = {'name':'Fixture.Foo','label':'foo','parameters':[], 'structure':False,
 'constructors':[{'name':'Fixture.Foo.a','ordinal':0,'fields':[]},
                 {'name':'Fixture.Foo.b','ordinal':1,'fields':[{'name':'n','shape':{'kind':'nat'}}]}]}
descriptor = {'format':'effect4-program-structure-v1','phase':'ground-source-declaration','blocks':[[family]]}
engine = 'type foo = Foo_a | Foo_b of int\nlet unused = 0\n'
common, gaps = selected_view(descriptor, engine)
assert len(common) == 1 and not gaps
assert common[0][2] == ['a','b']
print('PASS selected exact source/engine shape')

def refuses(name, d=descriptor, e=engine, a=()):
 try: selected_view(d,e,a)
 except ValueError: print('PASS refuses '+name)
 else: raise AssertionError(name+' accepted')

refuses('constructor reorder', e='type foo = Foo_b of int | Foo_a\n')
refuses('same-name payload change', e='type foo = Foo_a | Foo_b of bool\n')
refuses('unknown appended target constructor', e='type foo = Foo_a | Foo_b of int | Foo_c\n')
refuses('duplicate engine declaration', e=engine+'type foo = Foo_a\n')
refuses('unknown type shape', e='type foo = Foo_a | Foo_b of int -> int\n')
refuses('no selected target', e='type other = Other_x\n')
bad = copy.deepcopy(descriptor); bad['blocks'][0][0]['constructors'][1]['ordinal']=0
refuses('duplicate source ordinal',bad)
# The ordinal is the compiled declaration position. A sparse wire tag
# (tools/Effect4Gen/wire-tags.json) in its place is refused: the layout check reads layout.
bad = copy.deepcopy(descriptor); bad['blocks'][0][0]['constructors'][1]['ordinal']=4
refuses('a sparse wire tag in place of the declaration position',bad)
bad = copy.deepcopy(descriptor); bad['blocks'][0].append(copy.deepcopy(family))
refuses('duplicate source family',bad)
bad = copy.deepcopy(descriptor); bad['phase']='mono-lcnf'
refuses('wrong description phase',bad)
# The engine lagging the source refuses (tooling plan 4.2). This is the red control for the
# defect that let the engine run four `Ty` constructors behind for the whole of L5: the shortage
# used to be RECORDED in e4_program_layout.json, where nothing gated it.
refuses('an engine declaring fewer constructors than the source', e='type foo = Foo_a\n')
# Named in the allowance, the same shortage is recorded — and the record says it was allowed.
common, gaps = selected_view(descriptor,'type foo = Foo_a\n',['Fixture.Foo'])
assert common[0][2] == ['a'] and gaps[0]['reason'] == 'source-append-unavailable-in-frozen-engine'
assert gaps[0]['allowed'] is True and (gaps[0]['engine'], gaps[0]['source']) == (1, 2)
print('PASS an allowed engine lag is recorded, with the counts and the permission')
# And the allowance cannot go stale in either direction.
refuses('an allowance for a family that does not lag', a=['Fixture.Foo'])
refuses('an allowance for a family the source does not declare', a=['Fixture.Bar'])
# Real input can be read independently, but this alone is not a selected shape verdict.
actual = declarations((Path(__file__).resolve().parents[1]/'ocaml/engine/api_engine.ml').read_text())
assert actual and 'eff' in actual
print(f'PASS actual frozen engine reader: {len(actual)} declarations')
