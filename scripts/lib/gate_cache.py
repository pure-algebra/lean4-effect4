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

VERSION = 2


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


def file_inputs(root, names, optional=()):
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
        if name in optional and not path.exists():
            files[logical] = None
            continue
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


def output_of(root, command, strip=True):
    result = subprocess.run(command, cwd=root, check=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True)
    return result.stdout.strip() if strip else result.stdout


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
        if os.environ.get('OCAMLOPT'):
            commands['ocaml-override'] = [os.environ['OCAMLOPT'], '-version']
        commands['opam-packages'] = ['opam', 'list', '--switch=' + os.environ.get('OPAM_SWITCH', 'effect4'),
                                    '--installed', '--columns=name,version', '--short', '--color=never']
    return {name: output_of(root, command) for name, command in commands.items()}


def snapshot(root, inputs, runtime, environment, optional=()):
    return {'version': VERSION, 'inputs': file_inputs(root, inputs, optional),
            'host': [platform.system(), platform.machine()],
            'tools': tool_identity(root, runtime),
            'packages': package_state(root) if runtime != 'none' else {},
            'environment': {name: (os.environ[name].replace(str(Path(root).resolve()), '{root}')
                                   if name in os.environ else None)
                            for name in environment}}


def package_state(root):
    """Identify installed Git dependencies, including local edits beside their pinned commits."""
    manifest = Path(root) / 'lake-manifest.json'
    if not manifest.is_file():
        return {}
    data = json.loads(manifest.read_text(encoding='utf-8'))
    states = {}
    for package in data['packages']:
        if package['type'] != 'git':
            raise ValueError('content keys require a Git package: ' + package['name'])
        folder = Path(root) / data['packagesDir'] / package['name']
        head = output_of(folder, ['git', 'rev-parse', 'HEAD'])
        changed = output_of(folder, ['git', 'diff', '--no-ext-diff', '--name-only', '-z', 'HEAD', '--'], strip=False)
        added = output_of(folder, ['git', 'ls-files', '--others', '--exclude-standard', '-z'], strip=False)
        names = sorted(set(filter(None, (changed + '\0' + added).split('\0'))))
        states[package['name']] = {'head': head, 'changes': file_inputs(folder, names, names)}
    return states


def digest(value):
    return hashlib.sha256(json_bytes(value)).hexdigest()


def query_key(input_key, command):
    """Identify one host action over the prepared input snapshot."""
    return digest({'version': VERSION, 'input': input_key, 'command': list(command)})


def shared_store(root):
    common = Path(output_of(root, ['git', 'rev-parse', '--path-format=absolute', '--git-common-dir']))
    return common.parent / (common.name + '-checks')


def prepare(root, name, inputs, runtime='none', environment=(), outputs=()):
    """Write a fresh manifest and update the key only when its content identity changes."""
    root = Path(root)
    inputs = sorted(set(inputs) | set(outputs))
    state = snapshot(root, inputs, runtime, environment, outputs)
    request = {'name': name, 'inputs': sorted(set(inputs)), 'runtime': runtime,
               'environment': list(environment), 'optional': list(outputs),
               'snapshot': state, 'key': digest(state)}
    check = root / '.lake/check'
    write_changed(check / (name + '.inputs.json'), json_bytes(request))
    write_changed(check / (name + '.key'), (request['key'] + '\n').encode())
    return request['key']


def run(root, name, command, force=False, store=None):
    """Reuse a matching pass, or run the command and publish only an unchanged-input success."""
    flags = shlex.split(os.environ.get('MAKEFLAGS', ''))
    short = ''.join(flag.lstrip('-') for flag in flags
                    if not flag.startswith('--') and '=' not in flag and flag.lstrip('-').isalpha())
    if set(short) & set('ntq') or any(f in ('--dry-run', '--just-print', '--recon', '--touch', '--question') for f in flags):
        # GNU make executes recursive recipes even under -n/-t/-q. They cannot publish evidence.
        print(f'SKIP {name}: make requested no execution', flush=True)
        return 0
    force = force or 'B' in short or '--always-make' in flags
    root = Path(root)
    check = root / '.lake/check'
    request = json.loads((check / (name + '.inputs.json')).read_text())
    key = (check / (name + '.key')).read_text().strip()
    if request['name'] != name or key != request['key']:
        raise ValueError('check manifest and key disagree; regenerate the key')
    current = lambda: snapshot(root, request['inputs'], request['runtime'], request['environment'],
                               request.get('optional', ()))
    if digest(current()) != key:
        raise ValueError('check inputs changed after key preparation')
    store = Path(store) if store is not None else shared_store(root)
    expected_command = list(command)
    action_key = query_key(key, expected_command)
    result_path = store / name / action_key
    marker = check / name
    if not force and result_path.is_file():
        try:
            record = json.loads(result_path.read_text())
        except ValueError:
            record = {}
        if (record.get('key') == action_key and record.get('input') == key and
                record.get('command') == expected_command and record.get('exit') == 0):
            # A previous marker can hold the same bytes but predate the key's latest return.
            write_changed(marker, (key + '\n').encode())
            marker.touch()
            print(f'PASS {name}: shared result {action_key[:12]}', flush=True)
            return 0
    marker.unlink(missing_ok=True)
    started = time.monotonic()
    code = subprocess.run(command, cwd=root).returncode
    if code:
        return code
    if digest(current()) != key:
        raise ValueError('check inputs changed during its run; no pass recorded')
    record = {'version': VERSION, 'key': action_key, 'input': key,
              'command': expected_command, 'exit': 0,
              'seconds': round(time.monotonic() - started, 6)}
    write_changed(result_path, json_bytes(record))
    write_changed(marker, (key + '\n').encode())
    marker.touch()
    print(f'PASS {name}: recorded {action_key[:12]} ({record["seconds"]:.3f}s)', flush=True)
    return 0
