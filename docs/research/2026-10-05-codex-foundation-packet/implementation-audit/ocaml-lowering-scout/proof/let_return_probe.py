"""Finite mirror of evalT's let/variable/literal/fail fragment, not a Lean proof."""
import json

def run(fuel, env, expr):
    if fuel == 0:
        return ('outOfFuel',)
    tag, *args = expr
    if tag == 'int':
        return ('value', args[0])
    if tag == 'fail':
        return ('exn', args[0])
    if tag == 'var':
        for key, value in env:
            if key == args[0]:
                return ('value', value)
        return ('stuck', args[0])
    if tag == 'let':
        name, rhs, body = args
        value = run(fuel - 1, env, rhs)
        return run(fuel - 1, [(name, value[1])] + env, body) if value[0] == 'value' else value
    raise ValueError(tag)

cases = {
 'literal': ('int', 7),
 'shadowing': ('var', 'x'),
 'other variable': ('var', 'y'),
 'unbound': ('var', 'z'),
 'target exception': ('fail', 'failure'),
 'nested evaluation': ('let', 'y', ('int', 2), ('var', 'y')),
}
rows=[]
for name,e in cases.items():
    for n in range(4):
        env=[('x',99),('y',8)]
        lhs=run(n+2,env,('let','x',e,('var','x')))
        rhs=run(n+1,env,e)
        assert lhs == rhs
        rows.append({'case':name,'n':n,'result':lhs})
control={'fuel':1,'lhs':run(1,[],('let','x',('int',7),('var','x'))),'rhs':run(1,[],('int',7))}
assert control['lhs'] != control['rhs']
print(json.dumps({'evidence':'finite Python mirror of displayed Lean equations; not kernel checked','shifted_fuel_cases':rows,'same_fuel_countercontrol':control},indent=2))
