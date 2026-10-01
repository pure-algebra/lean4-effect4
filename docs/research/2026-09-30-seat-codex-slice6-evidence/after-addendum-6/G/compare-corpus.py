import hashlib,json,pathlib
here=pathlib.Path(__file__).resolve().parent
root=here.parents[4]
a=(here/'corpus-index.before.tsv').read_bytes();b=(root/'generated/corpus-index.tsv').read_bytes()
def rows(data):
 return {fields[0]:fields for line in data.decode().splitlines() if line and not line.startswith('#') for fields in [line.split('\t')]}
x,y=rows(a),rows(b)
changes=[{'program':k,'before':x.get(k),'after':y.get(k)} for k in sorted(set(x)|set(y)) if x.get(k)!=y.get(k)]
verdict=[d for d in changes if d['before'] is None or d['after'] is None or d['before'][1]!=d['after'][1]]
report={'before_sha256':hashlib.sha256(a).hexdigest(),'after_sha256':hashlib.sha256(b).hexdigest(),'before_rows':len(x),'after_rows':len(y),'byte_identical':a==b,'changes':changes,'verdict_changes':verdict,'evidence':'finite generated and wire corpus only'}
(here/'corpus-comparison.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
if verdict:raise SystemExit('STOP: review every changed acceptance verdict before proceeding')
