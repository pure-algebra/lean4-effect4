#!/usr/bin/env python3
"""Fresh current-Lean fixture map followed by the pinned TypeScript oracle."""
from pathlib import Path
import subprocess
import sys

out=Path(sys.argv[1]).resolve()
out.mkdir(parents=True,exist_ok=True)
fixture=out/'target-fixtures.json'
first=subprocess.run(['lake','env','lean','-M4096','--run','tools/Conform/Effect4/TargetFixtures.lean',str(fixture)])
if first.returncode:
    sys.exit(first.returncode)
sys.exit(subprocess.run(['bun','tools/target/conform.ts',str(fixture),str(out)]).returncode)
