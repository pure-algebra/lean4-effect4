#!/usr/bin/env python3
"""One production compiler checkpoint, used inside the fresh Conform runner."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts/lib'))
from conform_report import validate


def run(command):
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f'{command[0]} exited {result.returncode}\n{result.stdout[-4000:]}\n{result.stderr[-4000:]}')
    return result


def main(out):
    out = Path(out).resolve()
    run(['lake', 'env', 'lean', '-M4096', '--run', 'tools/Conform/Effect4/Normalization.lean', str(out)])
    for file in ['normalization.json', 'validity.json']:
        if validate(json.loads((out / file).read_text())):
            raise RuntimeError(f'{file}: checkpoint has unresolved or failed rows')
    compiler = os.environ.get('OCAMLOPT') or shutil.which('ocamlopt')
    if shutil.which('opam') and not os.environ.get('OCAMLOPT'):
        compiler = str(Path(run(['opam', 'var', 'bin', '--switch=effect4']).stdout.strip()) / 'ocamlopt')
    if not compiler:
        raise RuntimeError('ocamlopt is required for the compiler profile')
    run([compiler, '-w', '-a', str(out / 'normalization.ml'), '-o', str(out / 'normalization')])
    actual = run([str(out / 'normalization')]).stdout
    expected = (out / 'expected.txt').read_text()
    if actual != expected:
        raise RuntimeError('compiled OCaml observations differ from the Lean fixture list')
    (out / 'actual.txt').write_text(actual)
    # Mutate the actual emitted UTF-8 helper. Compiling must still succeed and the selected
    # program must report failure; a compiler failure is not a detected semantic mutation.
    text = (out / 'normalization.ml').read_text()
    original = 'Char.code (String.get s i)'
    if text.count(original) != 1:
        raise RuntimeError('UTF-8 mutation anchor missing or ambiguous')
    (out / 'mutated.ml').write_text(text.replace(original, '0'))
    run([compiler, '-w', '-a', str(out / 'mutated.ml'), '-o', str(out / 'mutated')])
    mutation = subprocess.run([str(out / 'mutated')], capture_output=True, text=True)
    if mutation.returncode != 1 or '\tFAIL' not in mutation.stderr:
        raise RuntimeError('UTF-8 mutation did not fail the selected observation')
    ids = [line.split('\t')[0] for line in expected.splitlines()] + ['utf8-mutation']
    if len(ids) != len(set(ids)):
        raise RuntimeError('duplicate host observation ID')
    required = [{'check':'normalization.ocaml','subject':{'kind':'fixture','path':[id]}} for id in ids]
    rows = [{**item,'outcome':'pass','evidence':'tested','message':'actual emitted OCaml observation matched', 'detail':None} for item in required]
    report = {'format':'conform-report-v2','tool':'conform.normalization.ocaml',
      'pins':[{'name':'ocaml','value':run([compiler,'-version']).stdout.strip()}], 'inputs':[],
      'expected':len(ids),'required':required,'rows':rows,
      'summary':{'rows':len(ids),'pass':len(ids),'refused':0,'counterexample':0,'unresolved':0,'complete':True,'exit':0}}
    validate(report, 0)
    (out / 'ocaml.json').write_text(json.dumps(report,indent=2)+'\n')
    (out / 'mutation.txt').write_text(mutation.stderr)
    for name in ['normalization','mutated']:
        for suffix in ['', '.cmi', '.cmx', '.o']:
            (out / (name + suffix)).unlink(missing_ok=True)
    print(f'compiler checkpoint: {len(ids)-1} actual OCaml checks and one emitted-code mutation passed')


if __name__ == '__main__':
    try:
        main(sys.argv[1])
    except (RuntimeError, OSError, ValueError) as error:
        print(error,file=sys.stderr)
        sys.exit(2)
