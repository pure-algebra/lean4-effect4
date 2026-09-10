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

def refuses(name, d=descriptor, e=engine):
 try: selected_view(d,e)
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
bad = copy.deepcopy(descriptor); bad['blocks'][0].append(copy.deepcopy(family))
refuses('duplicate source family',bad)
bad = copy.deepcopy(descriptor); bad['phase']='mono-lcnf'
refuses('wrong description phase',bad)
# Append shortages stay visible, never a generated missing arm or an execution pass.
common, gaps = selected_view(descriptor,'type foo = Foo_a\n')
assert common[0][2] == ['a'] and gaps[0]['reason'] == 'source-append-unavailable-in-frozen-engine'
print('PASS source append remains an explicit unavailable engine boundary')
# Real input can be read independently, but this alone is not a selected shape verdict.
actual = declarations((Path(__file__).resolve().parents[1]/'ocaml/engine/api_engine.ml').read_text())
assert actual and 'eff' in actual
print(f'PASS actual frozen engine reader: {len(actual)} declarations')
