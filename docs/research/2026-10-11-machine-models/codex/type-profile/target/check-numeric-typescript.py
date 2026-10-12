from pathlib import Path
import json, os, subprocess, sys
root=Path('/Users/pooks/.codex/worktrees/last-planned-goals/lean4-effect4')
sys.path.insert(0,str(root/'scripts'))
from lib import truth_host
bun, modules, _=truth_host.select(root,root/'harness/truth')
config=Path('/private/tmp/numeric-target-tsconfig.json')
config.write_text(json.dumps({
  'extends':str(root/'harness/truth/tsconfig.json'),
  'compilerOptions':{'typeRoots':[str(modules/'@types')]},
  'files':[str(root/'harness/truth/prelude.ts')],
  'include':[], 'exclude':[]
},indent=2)+'\n')
commands=[
 ('/private/tmp/profile-target-tsgo-version.log',truth_host.compiler(modules)+['--version']),
 ('/private/tmp/profile-target-tsgo.log',truth_host.compiler(modules)+['--project',str(config)]),
 ('/private/tmp/profile-target-atoms.log',[bun,'-e','''import { selfTestCases } from "./harness/truth/prelude.ts";
import { preludeInventoryFailures } from "./harness/truth/prelude-inventory.ts";
import { atomNames } from "./ts/eff/profile.gen.ts";
let failed = 0;
for (const c of selfTestCases) { const actual=c.apply(); const ok=actual===c.expected;
  console.log(`${ok ? "PASS" : "FAIL"} ${c.name}: ${String(actual)}`); if (!ok) failed++; }
for (const error of preludeInventoryFailures(atomNames,selfTestCases)) { console.log(`FAIL ${error}`); failed++; }
console.log(`${selfTestCases.length} atom controls; ${failed} failures`);
process.exitCode = failed ? 1 : 0;'''])]
for log,args in commands:
    with open(log,'w') as out:
        result=subprocess.run(args,cwd=root,stdout=out,stderr=subprocess.STDOUT)
    print(result.returncode,log,flush=True)
    if result.returncode:
        print(Path(log).read_text())
        sys.exit(result.returncode)
