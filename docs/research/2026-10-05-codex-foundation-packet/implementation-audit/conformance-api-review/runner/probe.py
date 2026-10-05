from pathlib import Path
import sys, json, importlib.util, subprocess, os, copy
from types import SimpleNamespace
sys.dont_write_bytecode = True
ROOT=Path('/Users/pooks/Dev/lean4-effect4')
OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'scripts/lib'))
from conform_report import validate, fresh_run, InvalidReport
results=[]
def report(ids=('selected',), outcome='pass'):
 required=[{'check':'probe', 'subject':{'kind':'fixture','path':[i]}} for i in ids]
 code=2 if outcome=='unresolved' else 0 if outcome=='pass' else 1
 return {'format':'conform-report-v2','tool':'isolated-probe','pins':[],'inputs':[],
  'expected':len(ids),'required':required,
  'rows':[{**r,'outcome':outcome,'evidence':'tested','message':'isolated validator input','detail':None} for r in required],
  'summary':{'rows':len(ids), 'pass':len(ids) if outcome=='pass' else 0,
  'refused':len(ids) if outcome=='refused' else 0,'counterexample':len(ids) if outcome=='counterexample' else 0,
  'unresolved':len(ids) if outcome=='unresolved' else 0,'complete':True,'exit':code}}
def record(name, observed, expected):
 assert observed==expected,(name,observed,expected)
 results.append({'name':name,'observed':observed,'expected':expected})
record('valid_report',validate(report(),0),0)
record('self_declared_empty_domain',validate(report(()),0),0)
try:
 validate(report(()),0,expected_ids=[('probe','fixture',('selected',))]); x='accepted'
except InvalidReport: x='rejected'
record('empty_domain_with_existing_expected_ids_API',x,'rejected')
bad=report();bad['rows']=[]
try:validate(bad);x='accepted'
except InvalidReport:x='rejected'
record('missing_row_positive_detector',x,'rejected')
producer=OUT/'producer.py'
producer.write_text('''from pathlib import Path
import sys,json
out=Path(sys.argv[1]); payload=json.loads(Path(sys.argv[2]).read_text())
for name,value in payload['files'].items():
 (out/name).write_text(json.dumps(value))
print('isolated producer diagnostic',file=sys.stderr)
sys.exit(payload['exit'])
''')
def fresh(name,files,expected,exit):
 d=OUT/name;d.mkdir(exist_ok=True)
 payload=d/'input.json';payload.write_text(json.dumps({'files':files,'exit':exit}))
 try:
  x=fresh_run([sys.executable,str(producer),'{out}',str(payload)],d/'receipt.json',expected,cwd=OUT,input_snapshot=lambda:{'stable':'a'*64})
  return x,d
 except InvalidReport as e:
  (d/'rejection.txt').write_text(str(e));return 'rejected',d
x,_=fresh('roles_control',{'one.json':report(),'two.json':report()},['one.json','two.json'],0)
record('two_valid_report_roles_control',x,0)
x,d=fresh('report_missing_format',{'one.json':report(),'two.json':{'rows':[]}},['one.json','two.json'],0)
record('second_expected_report_without_format_accepted',x,0)
record('unformatted_report_missing_from_validated_reports',list(json.loads((d/'receipt.json').read_text())['reports']),['one.json'])
x,d=fresh('report_demoted',{'one.json':report(),'two.json':{'format':'raw-artifact-v1','rows':[]}},['one.json','two.json'],0)
record('second_expected_report_treated_as_raw_artifact',x,0)
record('demoted_report_missing_from_validated_reports',list(json.loads((d/'receipt.json').read_text())['reports']),['one.json'])
x,d=fresh('reported_failure',{'one.json':report(outcome='refused')},['one.json'],1)
record('complete_reported_failure_retained',x,1)
record('complete_failure_receipt_exists',(d/'receipt.json').exists(),True)
x,d=fresh('incomplete_failure',{'failure.json':{'detail':'useful incomplete result'}},['one.json'],2)
record('incomplete_failure_rejected',x,'rejected')
record('incomplete_failure_artifacts_lost',not (d/'artifacts').exists() and not list(d.glob('.conform-*')),True)
spec=importlib.util.spec_from_file_location('checkpoint',ROOT/'scripts/check-conform.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
# Exercise the actual Python step's decision logic. All process calls below are mocks.
# No Lean, OCaml compiler, or generated executable is launched.
original_subprocess_run=m.subprocess.run
original_env=os.environ.get('OCAMLOPT')
os.environ['OCAMLOPT']='/isolated/mock/ocamlopt'
def step_case(name, mutation_code, mutation_stderr, actual='chosen\tPASS\n'):
 d=OUT/name;d.mkdir(exist_ok=True)
 for file in ('normalization.json','validity.json'):(d/file).write_text(json.dumps(report()))
 (d/'expected.txt').write_text('chosen\tPASS\n')
 (d/'normalization.ml').write_text('Char.code (String.get s i)\n')
 calls=[]
 def fake_run(command):
  calls.append(command)
  stdout='5.1.1\n' if command[-1]=='-version' else actual if command==[str(d/'normalization')] else ''
  return SimpleNamespace(returncode=0,stdout=stdout,stderr='')
 m.run=fake_run
 m.subprocess.run=lambda command,**kwargs: SimpleNamespace(returncode=mutation_code,stdout='',stderr=mutation_stderr)
 try:
  result=m.step_compiler(d); answer='accepted'
 except RuntimeError as e:
  answer='rejected';(d/'rejection.txt').write_text(str(e))
 finally:m.subprocess.run=original_subprocess_run
 (d/'mock-commands.json').write_text(json.dumps(calls,indent=2))
 return answer,d
try:
 x,d=step_case('mutation_selected_control',1,'chosen\tFAIL\n');record('selected_failure_accepted',x,'accepted')
 x,d=step_case('mutation_unrelated',1,'NOT-IN-THE-PLAN\tFAIL\n');record('unrelated_mutation_failure_accepted',x,'accepted')
 x,d=step_case('mutation_wrong_exit',2,'chosen\tFAIL\n');record('wrong_mutation_exit_rejected',x,'rejected')
 x,d=step_case('mutation_no_marker',1,'compiler error\n');record('failure_without_marker_rejected',x,'rejected')
 x,d=step_case('normal_mismatch',1,'chosen\tFAIL\n',actual='chosen\tWRONG\n');record('normal_output_mismatch_rejected',x,'rejected')
 record('normal_output_mismatch_not_written',(d/'actual.txt').exists(),False)
finally:
 m.subprocess.run=original_subprocess_run
 if original_env is None:os.environ.pop('OCAMLOPT',None)
 else:os.environ['OCAMLOPT']=original_env
(OUT/'probe-results.json').write_text(json.dumps({'python':sys.version,'scope':'actual Python validation/runner code; mocked compiler/Lean process outcomes; no host compiler execution','assertions':results},indent=2)+'\n')
print(json.dumps({'assertions':len(results),'all_expected_observations':True,'results':str(OUT/'probe-results.json')}))
