import json, os, pathlib, subprocess, sys, time
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[4]
tests=[
'Test/Counterexamples/Machine/Runtime/HostHandleForgery.lean',
'Test/Api/HostSessionContract.lean', 'Test/Api/KeyedHostContract.lean',
'Test/Api/ExternalContract.lean', 'Test/Api/AcquireHandleContract.lean',
'Test/Api/PackagesContract.lean', 'Test/Api/RunnerContract.lean',
'Test/Run/RunContract.lean', 'Test/Program/InvocationContract.lean',
'Test/Program/HostSpecContract.lean', 'Test/Program/LinkedRowsContract.lean']
commands=[('narrow', ROOT, ['lake','build',
'Effect4.Program.Admission','Effect4.Program.Compile','Effect4.Laws.Program.Admit',
'Effect4.Laws.Program.Handles.Hooks','Effect4.Laws.Program.CheckedTyping',
'Effect4.Laws.Run','Effect4.Laws.Api.HostSession'])]
commands += [(pathlib.Path(test).stem, ROOT, ['lake','env','lean','-DwarningAsError=true',test]) for test in tests]
commands += [('axioms',ROOT,['lake','env','lean','-DwarningAsError=true',str(HERE/'axioms.lean')]),
('dune',ROOT/'ocaml',['opam','exec','--switch=effect4','--','dune','build']),
('check-ocaml',ROOT,['make','check-ocaml'])]
results=[]
for name,cwd,cmd in commands:
    start=time.monotonic()
    attempt=1
    while (HERE/f'{name}-{attempt}.log').exists(): attempt+=1
    logpath=HERE/f'{name}-{attempt}.log'
    with logpath.open('w') as log:
        result=subprocess.run(cmd,cwd=cwd,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=log,stderr=subprocess.STDOUT)
    record=dict(name=name,cwd=str(cwd),command=cmd,exit=result.returncode,elapsed_seconds=round(time.monotonic()-start,2),log=logpath.name)
    results.append(record)
    (HERE/'checks-results.json').write_text(json.dumps(results,indent=2)+'\n')
    print(name,result.returncode,flush=True)
    if result.returncode: sys.exit(result.returncode)
    if name=='axioms' and any(x in logpath.read_text() for x in ['Classical.choice','sorryAx']):
        raise SystemExit('Unexpected axiom in final item A receipt')
