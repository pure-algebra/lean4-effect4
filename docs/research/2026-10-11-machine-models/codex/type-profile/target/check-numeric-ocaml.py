from pathlib import Path
import subprocess, sys
root = Path('/Users/pooks/.codex/worktrees/last-planned-goals/lean4-effect4/ocaml')
commands = [
 ('version', ['ocamlc', '-version']),
 ('build', ['dune','build','engine/test/test_engine.exe','engine/test/test_diff.exe','engine/test/e4_engine_bench.exe','gen/api_check.exe','engine/test/test_buckets.exe']),
 ('engine', ['dune','exec','./engine/test/test_engine.exe']),
 ('buckets', ['dune','exec','./engine/test/test_buckets.exe']),
 ('api', ['dune','exec','./gen/api_check.exe'])]
for stem in ['fibers_gen','machine_gen','api_gen']:
    commands.append(('warning8-'+stem, ['ocamlc','-w','+8','-warn-error','+8','-I','_build/default/clock/.effect4_clock.objs/byte','-c','-o','/private/tmp/Profile_'+stem+'.cmo','gen/'+stem+'.ml']))
for label, command in commands:
    log=Path('/private/tmp/profile-target-ocaml-'+label+'.log')
    args=['opam','exec','--switch=effect4','--']+command
    with log.open('w') as out:
        print('COMMAND:', ' '.join(args), file=out, flush=True)
        result=subprocess.run(args,cwd=root,stdout=out,stderr=subprocess.STDOUT)
    print(label, result.returncode, log, flush=True)
    if result.returncode:
        print(log.read_text())
        sys.exit(result.returncode)
