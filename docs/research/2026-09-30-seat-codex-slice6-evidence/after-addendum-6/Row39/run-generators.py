from pathlib import Path
import subprocess,sys
here=Path(__file__).resolve().parent
for group in ["derived","lcnf","eff","wire","cas"]:
    print("START",group,flush=True)
    result=subprocess.run([sys.executable,str(here/"check.py"),"gen-"+group,".","make","gen-"+group])
    if result.returncode:raise SystemExit(result.returncode)
print("ORDERED GENERATION COMPLETE",flush=True)
