#!/usr/bin/env python3
"""Retain one serialized, owner-requested acceptance command and its inputs."""
import datetime
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import sys
import time

ROOT = Path('/Users/pooks/.codex/worktrees/unguard/lean4-effect4')
OUT = Path('/private/tmp/codex-unguard/final-checks')
BASELINE = Path('/private/tmp/codex-unguard/protected-baseline.json')
BASE_COMMIT = 'c51f9e6b7c456d952d0fe408a274432f4c9aebd5'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def protected():
    return [dict(path=row['path'], expected=row['base_sha256'],
                 actual=digest(ROOT / row['path']))
            for row in json.loads(BASELINE.read_text())['paths']]

def unchanged(rows):
    return all(row['expected'] == row['actual'] for row in rows)

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()

def changed_inputs():
    changed = git('diff', '--name-only', BASE_COMMIT, '--').splitlines()
    untracked = git('ls-files', '--others', '--exclude-standard').splitlines()
    paths = sorted(set(changed + untracked))
    return {p: digest(ROOT / p) if (ROOT / p).is_file() else None for p in paths}

def main():
    if len(sys.argv) < 4 or sys.argv[2] != '--':
        raise SystemExit('usage: run-final-check.py NAME -- COMMAND [ARG ...]')
    name, command = sys.argv[1], sys.argv[3:]
    if not name or any(c not in 'abcdefghijklmnopqrstuvwxyz0123456789-_' for c in name):
        raise SystemExit('invalid evidence name')
    OUT.mkdir(exist_ok=True)
    log_path, result_path = OUT / (name + '.log'), OUT / (name + '.json')
    if log_path.exists() or result_path.exists():
        raise SystemExit('refusing to overwrite a retained attempt')
    before = protected()
    if not unchanged(before):
        raise SystemExit('a protected input differs before this command')
    branch, head = git('branch', '--show-current'), git('rev-parse', 'HEAD')
    if branch != 'codex/unguard':
        raise SystemExit('unexpected branch: ' + branch)
    inputs_before = changed_inputs()
    for lane in ['ts/eff/node_modules', 'harness/truth/node_modules']:
        if not (ROOT / lane).is_symlink() or not (ROOT / lane).is_dir():
            raise SystemExit('required existing dependency link missing: ' + lane)
    package = json.loads((ROOT / 'ts/eff/node_modules/@typescript/native-preview/package.json').read_text())
    if package['version'] != '7.0.0-dev.20260629.1':
        raise SystemExit('unexpected compiler version: ' + package['version'])
    full_command = ['scratch/lean-slot.sh', *command]
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    start = time.monotonic()
    with log_path.open('w') as output:
        output.write('COMMAND ' + shlex.join(full_command) + '\n')
        output.write('CWD ' + str(ROOT) + '\n')
        output.write('COMPILER ' + package['name'] + ' ' + package['version'] + '\n')
        output.flush()
        result = subprocess.run(full_command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    after = protected()
    record = dict(started=started, duration_seconds=round(time.monotonic()-start, 3),
                  cwd=str(ROOT), command=full_command, exit_code=result.returncode,
                  branch=branch, head=head, base=BASE_COMMIT,
                  lean_toolchain=(ROOT / 'lean-toolchain').read_text().strip(),
                  slot_script_sha256=digest(ROOT / 'scratch/lean-slot.sh'),
                  changed_inputs_before=inputs_before, changed_inputs_after=changed_inputs(),
                  compiler=dict(name=package['name'], version=package['version']),
                  protected_before=before, protected_after=after,
                  protected_unchanged=unchanged(after), log=str(log_path), log_sha256=digest(log_path))
    result_path.write_text(json.dumps(record, indent=2) + '\n')
    lines = log_path.read_text(errors='replace').splitlines()
    print('\n'.join(lines[-55:]))
    print(json.dumps({k:record[k] for k in ['duration_seconds','exit_code','protected_unchanged','log']}))
    raise SystemExit(result.returncode if result.returncode else (0 if unchanged(after) else 91))

if __name__ == '__main__':
    main()
