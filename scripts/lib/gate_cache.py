"""Content identity and successful-result reuse for Make checks.

Make owns ordering and commands. This module owns content keys and atomic result records.
Properties: paths are relative, input times are irrelevant, failures never publish a pass,
and a changed input during a command refuses publication. Stores are shared only within a
Git common directory; host and tool identities are part of each key.
"""
import hashlib
import json
import os
import platform
import shlex
import subprocess
import sys
import tempfile
import time
from pathlib import Path

VERSION = 1


def json_bytes(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def write_changed(path, content):
    """Atomically replace a file only when its bytes differ, preserving Make's stamp idiom."""
    path = Path(path)
    if path.is_file() and path.read_bytes() == content:
        return False
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=path.name + '.', dir=path.parent)
    try:
        with os.fdopen(descriptor, 'wb') as output:
            output.write(content)
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)
    return True


def file_inputs(root, names):
    """Hash named files and directory inventories by logical path, following file links.

    Callers select directories explicitly. Missing inputs and directory links refuse: a
    caller must name the resolved install's actual input files, not hash a mutable install tree.
    """
    root = Path(root).absolute()
    files = {}
    for name in sorted(set(names)):
        path = Path(name)
        path = path if path.is_absolute() else root / path
        logical = path.relative_to(root).as_posix() if path.is_relative_to(root) else '@external/' + path.as_posix()
        if path.is_dir():
            if path.is_symlink():
                raise ValueError(f'directory link is not a file input: {logical}')
            entries = sorted(path.rglob('*'))
            files[logical + '/'] = None
            for entry in entries:
                if entry.is_symlink() and entry.is_dir():
                    raise ValueError(f'directory link is not a file input: {entry}')
                if entry.is_file():
                    name = logical.rstrip('/') + '/' + entry.relative_to(path).as_posix()
                    files[name] = hashlib.sha256(entry.read_bytes()).hexdigest()
        else:
            files[logical] = hashlib.sha256(path.read_bytes()).hexdigest()
    return files


def output_of(root, command):
    result = subprocess.run(command, cwd=root, check=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True)
    return result.stdout.strip()


def tool_identity(root, runtime):
    commands = {'python': [sys.executable, '--version']}
    if runtime in ('lean', 'ts', 'ocaml', 'all'):
        commands['lean'] = shlex.split(os.environ.get('LAKE', 'lake')) + ['env', 'lean', '--version']
    if runtime in ('ts', 'all'):
        commands['node'] = shlex.split(os.environ.get('EFFECT4_NODE', os.environ.get('NODE', 'node'))) + ['--version']
        commands['bun'] = shlex.split(os.environ.get('EFFECT4_BUN', os.environ.get('BUN', 'bun'))) + ['--version']
    if runtime in ('ocaml', 'all'):
        prefix = shlex.split(os.environ.get('OCAML',
            'opam exec --switch=' + os.environ.get('OPAM_SWITCH', 'effect4') + ' --'))
        commands['ocaml'] = prefix + ['ocamlopt', '-version']
        commands['dune'] = prefix + ['dune', '--version']
    return {name: output_of(root, command) for name, command in commands.items()}


def snapshot(root, inputs, runtime, environment):
    return {'version': VERSION, 'inputs': file_inputs(root, inputs),
            'host': [platform.system(), platform.machine()],
            'tools': tool_identity(root, runtime),
            'environment': {name: os.environ.get(name, '').replace(str(Path(root).resolve()), '{root}')
                            for name in environment}}


def digest(value):
    return hashlib.sha256(json_bytes(value)).hexdigest()


def shared_store(root):
    common = Path(output_of(root, ['git', 'rev-parse', '--path-format=absolute', '--git-common-dir']))
    return common.parent / (common.name + '-checks')


def prepare(root, name, inputs, runtime='none', environment=()):
    """Write a fresh manifest and update the key only when its content identity changes."""
    root = Path(root)
    state = snapshot(root, inputs, runtime, environment)
    request = {'name': name, 'inputs': sorted(set(inputs)), 'runtime': runtime,
               'environment': list(environment), 'snapshot': state, 'key': digest(state)}
    check = root / '.lake/check'
    write_changed(check / (name + '.inputs.json'), json_bytes(request))
    write_changed(check / (name + '.key'), (request['key'] + '\n').encode())
    return request['key']


def run(root, name, command, force=False, store=None):
    """Reuse a matching pass, or run the command and publish only an unchanged-input success."""
    root = Path(root)
    check = root / '.lake/check'
    request = json.loads((check / (name + '.inputs.json')).read_text())
    key = (check / (name + '.key')).read_text().strip()
    if request['name'] != name or key != request['key']:
        raise ValueError('check manifest and key disagree; regenerate the key')
    current = lambda: snapshot(root, request['inputs'], request['runtime'], request['environment'])
    if digest(current()) != key:
        raise ValueError('check inputs changed after key preparation')
    store = Path(store) if store is not None else shared_store(root)
    result_path = store / name / key
    marker = check / name
    expected_command = list(command)
    if not force and result_path.is_file():
        try:
            record = json.loads(result_path.read_text())
        except ValueError:
            record = {}
        if record.get('key') == key and record.get('command') == expected_command and record.get('exit') == 0:
            # A previous marker can hold the same bytes but predate the key's latest return.
            write_changed(marker, (key + '\n').encode())
            marker.touch()
            print(f'PASS {name}: shared result {key[:12]}', flush=True)
            return 0
    marker.unlink(missing_ok=True)
    started = time.monotonic()
    code = subprocess.run(command, cwd=root).returncode
    if code:
        return code
    if digest(current()) != key:
        raise ValueError('check inputs changed during its run; no pass recorded')
    record = {'version': VERSION, 'key': key, 'command': expected_command, 'exit': 0,
              'seconds': round(time.monotonic() - started, 6)}
    write_changed(result_path, json_bytes(record))
    write_changed(marker, (key + '\n').encode())
    marker.touch()
    print(f'PASS {name}: recorded {key[:12]} ({record["seconds"]:.3f}s)', flush=True)
    return 0
