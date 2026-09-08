#!/usr/bin/env python3
"""Exercise the arm-map wrapper's real policy and cache in an isolated tree."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parent.parent
with tempfile.TemporaryDirectory(prefix='effect4-armmap-policy-') as directory:
    work = Path(directory)
    for name in ['check-armmap-citations.sh', 'lib/portable.sh', 'lib/stamp.sh', 'lib/known-red.sh']:
        target = work / 'scripts' / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / 'scripts' / name, target)
    policy = work / 'Test/fixtures/trust-gate/known-red.txt'
    policy.parent.mkdir(parents=True)
    checker = work / 'scripts/check-armmap-citations.py'
    checker.write_text(
        'import os, pathlib, sys\n'
        'with pathlib.Path("runs").open("a") as f: f.write("run\\n")\n'
        'print("fixture checker diagnostic")\n'
        'sys.exit(int(os.environ["ARM_POLICY_TEST_EXIT"]))\n')
    env = {**os.environ, 'EFFECT4_FORCE': '0'}

    def check(label, declared, observed, accepted, diagnostic):
        policy.write_text('# reason: fixture debt\n# gate: armmap-citations\n' if declared else '')
        result = subprocess.run(['bash', 'scripts/check-armmap-citations.sh'], cwd=work,
                                env={**env, 'ARM_POLICY_TEST_EXIT': str(observed)},
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert (result.returncode == 0) == accepted, (label, result.stdout)
        assert diagnostic in result.stdout, (label, result.stdout)
        print('PASS armmap policy:', label)

    check('undeclared drift refuses', False, 3, False, 'UNDECLARED FAILURE')
    check('declared drift is reported', True, 3, True, 'red as declared')
    runs = (work / 'runs').read_text()
    check('declared drift executes again', True, 3, True, 'red as declared')
    assert (work / 'runs').read_text() == runs + 'run\n'
    assert not (work / '.lake/stamps/armmap-citations').exists()
    check('declared unexpected pass refuses', True, 0, False, 'UNEXPECTED PASS')
    check('broken checker still refuses', True, 2, False, 'checker failed (exit 2)')
    check('undeclared green stamps', False, 0, True, 'fixture checker diagnostic')
    runs = (work / 'runs').read_text()
    check('unchanged green uses its stamp', False, 0, True, 'skipped')
    assert (work / 'runs').read_text() == runs
    check('adding a declaration invalidates green', True, 0, False, 'UNEXPECTED PASS')
