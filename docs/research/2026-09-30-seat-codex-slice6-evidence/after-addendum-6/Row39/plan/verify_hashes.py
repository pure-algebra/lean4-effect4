from pathlib import Path
import hashlib,json,sys
base=Path(__file__).resolve().parent
if len(sys.argv)!=3:raise SystemExit('usage: python3 verify_hashes.py STAGE_NUMBER_OR_NAME TARGET_TREE')
meta=json.loads((base/'series.json').read_text())
choice=sys.argv[1]
stage=meta['stages'][int(choice)-1] if choice.isdigit() else next(s for s in meta['stages'] if s['stage']==choice)
root=Path(sys.argv[2]);errors=[]
for row in stage['changes']:
    p=root/row['path']
    actual=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
    if actual!=row['old_sha256']:errors.append({'path':row['path'],'expected':row['old_sha256'],'actual':actual})
    elif p.is_file() and (p.stat().st_mode&0o111)!=(int(row['mode'],8)&0o111):errors.append({'path':row['path'],'error':'executable mode differs'})
print(json.dumps({'stage':stage['stage'],'matching':not errors,'errors':errors},indent=2))
raise SystemExit(bool(errors))
