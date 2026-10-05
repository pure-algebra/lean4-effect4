import json,pathlib,sys
out=pathlib.Path(sys.argv[1]);mode=sys.argv[2]
r={'format':'conform-report-v2','tool':'fixture','pins':[],'inputs':[],
   'expected':1,'required':[{'check':'fixture.check','subject':{'kind':'fixture','path':['a']}}],
   'rows':[{'check':'fixture.check','subject':{'kind':'fixture','path':['a']},'outcome':'pass','evidence':'tested','message':'ok','detail':None}],
   'summary':{'rows':1,'pass':1,'refused':0,'counterexample':0,'unresolved':0,'complete':True,'exit':0}}
(out/'one.json').write_text(json.dumps(r))
if mode=='both': other=r
elif mode=='removed-report-tag': other={'note':'This file no longer contains a report.'}
elif mode=='bad-report-tag': other={**r,'format':'conform-report-v999'}
elif mode=='missing-file': sys.exit(0)
else: raise ValueError(mode)
(out/'two.json').write_text(json.dumps(other))
