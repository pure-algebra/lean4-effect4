#!/usr/bin/env python3
"""Prepare and check four-module H2 patch; --apply is explicit and never used by this seat.
Do not apply until serialized compilation, controls, and scope review are complete.
This script does not include or authorize proposed test migrations.
"""
import argparse,difflib,hashlib,json,subprocess
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--source',default='/Users/pooks/Dev/lean4-effect4-slice6')
ap.add_argument('--mechanical',default='/private/tmp/h2-part-one-candidate')
ap.add_argument('--repaired',default='/private/tmp/h2-part-one-repaired')
ap.add_argument('--out',default='/private/tmp/h2-part-one-candidate/for-apply')
ap.add_argument('--apply',action='store_true')
a=ap.parse_args();source=Path(a.source).resolve();mechanical=Path(a.mechanical).resolve();repaired=Path(a.repaired).resolve();out=Path(a.out).resolve()
if not out.is_relative_to(Path('/private/tmp')):raise RuntimeError('output must be under /private/tmp')
manifest=json.loads((mechanical/'source-manifest.json').read_text())
repairs=json.loads((repaired/'eight-body-manifest.json').read_text())
allowed={i['declaration'] for i in manifest['authorized_existing_bodies']}
actual={i['declaration'] for i in repairs['existing_bodies']}
if len(actual)!=8 or actual!=allowed:raise RuntimeError('repair manifest does not name exactly authorized8')
prefix=Path('src/Effect4/Laws/Program/Typed')
if (source/prefix/'Scheduler.lean').exists():raise RuntimeError('H1 Scheduler now exists: regenerate and report added exit positions before applying')
hashfile=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
if hashfile(source/prefix/'Membership.lean')!=manifest['membership_sha256']:raise RuntimeError('Membership changed since preparation')
patch=[];files={}
for module,entry in manifest['modules'].items():
    rel=Path(entry['path']);path=source/rel
    if hashfile(path)!=entry['input_sha256']:raise RuntimeError('source drift: '+str(rel))
    old=path.read_text();new=(repaired/rel).read_text()
    if module=='Stack':
        before='cause (`U-01`), which carries no `Fail` and so fits every type.'
        after='cause (`U-01`), which carries no `Fail`. Its original typed exit and recorded-interrupt\nprovenance separately supply the part-one defect exclusion.'
        if new.count(before)!=1:raise RuntimeError('Stack module doc anchor drift')
        new=new.replace(before,after,1)
    dest=out/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(new)
    files[str(rel)]={'before_sha256':entry['input_sha256'],'after_sha256':hashlib.sha256(new.encode()).hexdigest()}
    patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+str(rel),tofile='b/'+str(rel)))
out.mkdir(parents=True,exist_ok=True);patchfile=out/'core.patch';patchfile.write_text(''.join(patch))
(out/'apply-manifest.json').write_text(json.dumps({'files':files,'new_helpers':repairs['new_helpers'],
    'authorized_existing_bodies':sorted(actual),'membership_sha256':manifest['membership_sha256'],
    'validation':'git apply --check only; no Lean executed by this script','source_root':str(source)},indent=2)+'\n')
subprocess.run(['git','apply','--check',str(patchfile)],cwd=source,check=True)
if a.apply:
    subprocess.run(['git','apply',str(patchfile)],cwd=source,check=True)
print(json.dumps({'patch':str(patchfile),'apply_check':'passed','repository_written':a.apply,
                  'warning':'Not integrated: fresh Lean measurements, tests, axioms, and strict ninth-body scope check still required.'},indent=2))
