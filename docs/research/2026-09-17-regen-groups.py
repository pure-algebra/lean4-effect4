#!/usr/bin/env python3
"""Run generator groups by hand, in order: build each group's imports, then run it."""
import json, subprocess, sys
repo = "/Users/pooks/Dev/lean4-effect4"
raw = subprocess.run(["lake","env","lean","--run","tools/Effect4Gen/Driver.lean","--commands"],cwd=repo,capture_output=True,text=True).stdout
groups = {g["name"]: g for g in json.loads(raw)}
for name in sys.argv[1:]:
    g = groups[name]; args = [a.replace("\\","/") for a in g["args"]]
    imports = args[args.index("--imports")+1].split(",") if "--imports" in args else []
    if imports:
        r = subprocess.run(["lake","build",*imports],cwd=repo,capture_output=True,text=True)
        if r.returncode != 0:
            errs=[l for l in (r.stdout+r.stderr).split("\n") if "error" in l][:8]
            print(f"[{name}] imports failed to build:", *errs, sep="\n  "); sys.exit(1)
    r = subprocess.run(["lake",*args],cwd=repo,capture_output=True,text=True)
    tail = (r.stdout+r.stderr).strip().split("\n")[-2:]
    print(f"[{name}] exit={r.returncode}", *tail, sep="\n  ")
    if r.returncode != 0: sys.exit(1)
