from pathlib import Path
import datetime, hashlib, json, subprocess
r=Path(__file__).resolve().parent
review=r.parents[2]
primary=Path("/Users/pooks/Dev/lean4-effect4")
roots=[primary/".lake/build/lib/lean"]+sorted((primary/".lake/packages").glob("*/.lake/build/lib/lean"))
overlay=review/".lake/co6b-public-review"
overlay.mkdir(exist_ok=True)
seen={}; std=set(); todo=["Effect4.Api"]
while todo:
    name=todo.pop()
    if name in seen or name in std: continue
    path=Path(*name.split("."))
    base=next((base for base in roots if (base/path.with_suffix(".olean")).exists()),None)
    if base is None:
        assert name=="Init" or name=="Std" or name=="Lean" or name.startswith(("Init.","Std.","Lean.")), name
        std.add(name); continue
    p=base/path.with_suffix(".olean")
    ilean=p.with_suffix(".ilean")
    assert ilean.exists(), name
    data=json.loads(ilean.read_text())
    todo += [entry[0] for entry in data["directImports"]]
    seen[name]=p
artifacts=[]
for name,p in sorted(seen.items()):
    dst=overlay/Path(*name.split(".")).with_suffix(".olean")
    dst.parent.mkdir(parents=True,exist_ok=True)
    for src in [p, p.with_suffix(".ilean"), Path(str(p)+".private"), Path(str(p)+".server"), p.with_suffix(".ir"), p.with_suffix(".ir.sig")]:
        if not src.exists(): continue
        target=dst.parent/src.name
        before=src.stat()
        subprocess.run(["cp","-c",str(src),str(target)],check=True)
        digest=hashlib.sha256(target.read_bytes()).hexdigest()
        after=src.stat()
        assert (before.st_size,before.st_mtime_ns)==(after.st_size,after.st_mtime_ns), str(src)
        artifacts.append({"module":name,"source":str(src),"target":str(target.relative_to(review)),"sha256":digest,"bytes":target.stat().st_size})
sources=[]
for name in ["src/Effect4/Program/Eff.lean","src/Effect4/Codegen/Print.lean","src/Effect4/Codegen/Read.lean","src/Effect4/Codegen/Admit.lean","src/Effect4/Codegen/Checked.lean","src/Effect4/Api.lean","Test/Codegen/ServicesPrint.lean"]:
    data=(primary/name).read_bytes(); target=r/"snapshot"/name
    target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(data)
    sources.append({"path":name,"sha256":hashlib.sha256(data).hexdigest()})
manifest={"captured_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"primary_head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=primary,text=True).strip(),"toolchain":(primary/"lean-toolchain").read_text().strip(),"artifact_origin":"Builder outputs; critical entries are recompiled independently by compile.py.","standard_library":sorted(std),"sources":sources,"artifacts":artifacts}
(r/"pins.json").write_text(json.dumps(manifest,indent=2)+"\n")
print(json.dumps({"modules":len(seen),"artifact_megabytes":sum(a["bytes"] for a in artifacts)/1e6,"head":manifest["primary_head"]}),flush=True)
