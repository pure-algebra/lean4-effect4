import json, os, pathlib, shlex, subprocess, tempfile
ROOT=pathlib.Path(__file__).resolve().parents[5]
def run(args, capture=False):
    print('+ '+shlex.join(args), flush=True)
    return subprocess.run(args, cwd=ROOT, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True, text=True, stdout=subprocess.PIPE if capture else None).stdout
rows=json.loads(run(['lake','env','lean','-DwarningAsError=true','-M4096','--run','tools/Effect4Gen/Driver.lean','--commands'], True))
row=next(row for row in rows if row['out']=='src/Effect4/Api/RunnerDerived.lean')
args=list(row['args'])
args[args.index('--append')+1]=args[args.index('--append')+1].replace(chr(92), '/')
with tempfile.TemporaryDirectory(prefix='effect4-a-runner-') as temporary:
    output=pathlib.Path(temporary)/'RunnerDerived.lean'
    args[args.index('--out')+1]=str(output)
    args+=['--header-out',row['out']]
    args.insert(2, '-DwarningAsError=true')
    run(['lake',*args])
    (ROOT/row['out']).write_bytes(output.read_bytes())
