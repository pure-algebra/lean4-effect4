from pathlib import Path
import json, os, shutil, subprocess, tempfile
r=Path(__file__).resolve().parent; logs=r/"checks"
primary=Path("/Users/pooks/Dev/lean4-effect4")
commit="294c89cdee0fd5874c01df45fb2654c5a480b2cd"
def source(path):
    return subprocess.check_output(["git","show",commit+":"+path],cwd=primary)
with tempfile.TemporaryDirectory(prefix="shell-",dir=logs) as td:
    work=Path(td)
    for d in ["src","Test","tools/Conform","src/OCaml5/Lcnf","src/OCaml5/Ml","scripts"]:
        (work/d).mkdir(parents=True,exist_ok=True)
    for f in ["Makefile","scripts/lean-imports.py"]:
        (work/f).write_bytes((r/"snapshot"/f).read_bytes())
    for f in ["src/Effect4/Api/HostProtocol.lean","src/Effect4/Program/Profile.lean","tools/Tools/GeneratedStamp.lean"]:
        p=work/f;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b"")
    (work/"ImportProbe.mk").write_text("probe:\n\t$(call build_imports,$(PROBE_FILE))\n")
    (work/"lake-stub.py").write_text("import json,sys\nprint('CAPTURED_LAKE_ARGS='+json.dumps(sys.argv[1:]))\n")
    consumer=source("tools/Tools/HostProtocol.lean").decode()
    outcomes=[]
    cases=[("current",consumer),("leading_comment","/- Ordinary header comment. -/\n"+consumer),("missing_file",None)]
    for label,text in cases:
        fixture=work/(label+".lean")
        if text is not None: fixture.write_text(text)
        cmd=["make","-s","-f","Makefile","-f","ImportProbe.mk","probe","LAKE=python3 "+str(work/"lake-stub.py"),"PROBE_FILE="+str(fixture)]
        p=subprocess.run(cmd,cwd=work,text=True,capture_output=True)
        lines=[l for l in p.stdout.splitlines() if l.startswith('CAPTURED_LAKE_ARGS=')]
        args=json.loads(lines[0].split('=',1)[1]) if lines else None
        assert p.returncode==0 and args and args[0]=='build',(label,p.stdout,p.stderr)
        assert (len(args)>1)==(label=='current'),(label,args)
        (logs/("shell-"+label+".log")).write_text(p.stdout+p.stderr)
        outcomes.append({"case":label,"make_exit":p.returncode,"captured_lake_args":args,"actual_lake_executed":False})
    (logs/"shell-controls.json").write_text(json.dumps(outcomes,indent=2)+"\n")
    print(json.dumps(outcomes,indent=2))
cmd=["python3","scripts/test-lean-imports.py"]
p=subprocess.run(cmd,cwd=primary,env={**os.environ,"PYTHONDONTWRITEBYTECODE":"1"},text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(logs/"shared-import-tests.log").write_text(p.stdout)
(logs/"shared-import-tests.json").write_text(json.dumps({"command":cmd,"cwd":str(primary),"exit_code":p.returncode},indent=2)+"\n")
print(p.stdout)
assert p.returncode==0
