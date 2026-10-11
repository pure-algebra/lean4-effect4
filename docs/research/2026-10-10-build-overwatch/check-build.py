from pathlib import Path
import hashlib, json, os, runpy, shutil, subprocess, tempfile
r=Path(__file__).resolve().parent
primary=Path("/Users/pooks/Dev/lean4-effect4")
commit="294c89cdee0fd5874c01df45fb2654c5a480b2cd"
logs=r/"checks"; logs.mkdir(exist_ok=True)
def gitfile(path):
    return subprocess.check_output(["git","show",commit+":"+path],cwd=primary)
paths=subprocess.check_output(["git","ls-tree","-r","--name-only",commit],cwd=primary,text=True).splitlines()
with tempfile.TemporaryDirectory(prefix="make-",dir=logs) as td:
    work=Path(td)
    inventory=[p for p in paths if ((p.startswith(("src/","Test/")) and p.endswith(".lean")) or (p.startswith("tools/Conform/") and p.endswith((".lean",".json"))) or p in ["scripts/check-conform.py","scripts/lib/conform_report.py","lean-toolchain","lakefile.toml","lake-manifest.json"])]
    for name in inventory:
        p=work/name; p.parent.mkdir(parents=True,exist_ok=True)
        p.write_bytes(b""); os.utime(p,(1000000000,1000000000))
    shutil.copyfile(r/"snapshot/Makefile",work/"Makefile")
    marker=work/".lake/check/cases"; marker.parent.mkdir(parents=True,exist_ok=True)
    marker.write_text("already checked\n"); os.utime(marker,(1100000000,1100000000))
    cases=[("unchanged",None,False),("core_source","src/Effect4.lean",True),("checker_source","scripts/check-conform.py",True),("toolchain_pin","lean-toolchain",False),("package_pin","lake-manifest.json",False),("lake_configuration","lakefile.toml",False)]
    results=[]
    for label,changed,expected_observed in cases:
        cmd=["make","-n","check-cases"]+(["-W",changed] if changed else [])
        p=subprocess.run(cmd,cwd=work,text=True,capture_output=True)
        runs="scripts/check-conform.py cases" in p.stdout
        (logs/("make-"+label+".log")).write_text(p.stdout+p.stderr)
        assert p.returncode==0,(label,p.stderr)
        assert runs==expected_observed,(label,p.stdout)
        results.append({"case":label,"command":cmd,"exit_code":p.returncode,"runs_gate":runs,"should_run":changed is not None})
    (work/"PinsProbe.mk").write_text(".lake/check/cases .lake/check/native .lake/check/compiler: lean-toolchain lakefile.toml lake-manifest.json\n")
    repaired=[]
    for label,changed,_ in cases:
        cmd=["make","-n","-f","Makefile","-f","PinsProbe.mk","check-cases"]+(["-W",changed] if changed else [])
        p=subprocess.run(cmd,cwd=work,text=True,capture_output=True)
        runs="scripts/check-conform.py cases" in p.stdout
        assert p.returncode==0 and runs==(changed is not None),(label,p.stdout,p.stderr)
        repaired.append({"case":label,"runs_gate":runs})
    (logs/"make-repair-controls.json").write_text(json.dumps(repaired,indent=2)+"\n")
    (logs/"make-controls.json").write_text(json.dumps({"reviewed_commit":commit,"makefile_sha256":hashlib.sha256((work/"Makefile").read_bytes()).hexdigest(),"inventory_files":len(inventory),"method":"Unmodified Makefile; isolated path inventory with empty source bytes and controlled old timestamps. Dry runs only.","results":results},indent=2)+"\n")
    print(json.dumps(results,indent=2))
new=runpy.run_path(str(r/"snapshot/scripts/lean-imports.py"))
common_path=r/"snapshot/scripts/lib/lean_imports.py"
common_path.parent.mkdir(parents=True,exist_ok=True); common_path.write_bytes(gitfile("scripts/lib/lean_imports.py"))
shared=runpy.run_path(str(common_path))
source=gitfile("tools/Tools/HostProtocol.lean").decode()
fixture=r/"ImportControls.lean"
variants={"current_consumer":source,"leading_block_comment":"/- Ordinary leading comment. -/\n"+source,"between_imports":source.replace("import Lean.Data.Json","/- Ordinary header comment. -/\nimport Lean.Data.Json")}
import_results=[]
for label,text in variants.items():
    fixture.write_text(text)
    got=new['imports'](fixture); expected=shared['header_imports'](text)
    import_results.append({"case":label,"current_reader":got,"shared_reader":expected})
fixture.write_text("/- A legal comment before imports. -/\nimport ProofGraph.GoalTag\nimport Lean\n")
assert import_results[0]['current_reader']==import_results[0]['shared_reader']
assert import_results[1]['current_reader']==[] and len(import_results[1]['shared_reader'])==4
assert len(import_results[2]['current_reader'])==2 and len(import_results[2]['shared_reader'])==4
(logs/"import-controls.json").write_text(json.dumps(import_results,indent=2)+"\n")
print(json.dumps(import_results,indent=2))
