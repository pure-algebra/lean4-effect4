import json
from pathlib import Path
p=Path(__file__).parent/'emitted'/'todo.table.json'
t=json.load(open(p))
allowed={'nat','string','bool','unit','never','lit'}
def cf(x):
 k=x['_tag']
 if k in allowed:return True
 if k in {'list','option'}:return cf(x['inner'])
 if k=='prod':return cf(x['left']) and cf(x['right'])
 if k=='record':return all(cf(v[1]) for _,v in x['fields'])
 raise ValueError('Unexpected type '+k)
results=[{'name':r['name'],'answer':cf(r['answer']),'error':cf(r['error']),'typeArgs':r['typeArgs']} for r in t['table']]
print(json.dumps(results))
assert all(r['answer'] and r['error'] for r in results)
