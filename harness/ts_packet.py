"""Shared setup for exact emitted TypeScript packets; caller observations stay in each runner."""
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EFFECT = '4.0.1'
COMPILER = '7.0.0-dev.20260629.1'
PRELUDE_FILES = ['prelude-atoms.gen.ts', 'records.ts', 'tuples.ts']


def run(command, cwd=ROOT, timeout=300):
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=timeout,
                            env={**os.environ, 'LEAN_NUM_THREADS': '3'})
    if result.returncode:
        raise RuntimeError(f'{command}: exit {result.returncode}\n{result.stdout}{result.stderr}')
    return result.stdout


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare_output(install, output):
    """Check the caller-selected pins and refuse an occupied evidence directory."""
    install, output = install.resolve(), output.resolve()
    for name, expected in [('effect', EFFECT), ('@typescript/native-preview', COMPILER)]:
        if json.loads((install / name / 'package.json').read_text())['version'] != expected:
            raise RuntimeError(f'Wrong installed {name} version')
    if output.exists() and any(output.iterdir()):
        raise RuntimeError('Refuse to overwrite retained evidence')
    output.mkdir(parents=True, exist_ok=True)
    return install, output


@contextmanager
def compiled_packet(install, output, files, observer, prefix):
    """Compile the exact declarations with their helper imports in a temporary dependency environment."""
    with tempfile.TemporaryDirectory(prefix=prefix) as temp:
        work = Path(temp)
        (work / 'node_modules').symlink_to(install, target_is_directory=True)
        for name in PRELUDE_FILES:
            shutil.copyfile(ROOT / 'harness/truth' / name, work / name)
        (work / 'prelude.ts').write_text(''.join(f'export * from "./{name}"\n' for name in PRELUDE_FILES))
        helpers = run(['bun', '--no-install', '-e',
                       'import * as H from "./prelude.ts"; console.log(Object.keys(H).join(", "))'], cwd=work).strip()
        header = 'import { Cause, Context, Data, Deferred, Effect, Exit, Fiber, Layer, Option, Ref, Scope, pipe } from "effect"\n'
        header += f'import {{ {helpers} }} from "./prelude.ts"\n'
        for name in files:
            (work / name).write_text(header + (output / name).read_text())
        shutil.copyfile(observer, work / 'observe.ts')
        shutil.copyfile(output / 'manifest.json', work / 'manifest.json')
        config = {'compilerOptions': {'target': 'ES2022', 'module': 'ESNext', 'moduleResolution': 'bundler',
                  'strict': True, 'exactOptionalPropertyTypes': True, 'noUncheckedIndexedAccess': True,
                  'verbatimModuleSyntax': True, 'allowImportingTsExtensions': True, 'noEmit': True,
                  'skipLibCheck': True, 'types': ['bun']},
                  'files': files + ['observe.ts'], 'include': []}
        (work / 'tsconfig.json').write_text(json.dumps(config, indent=2) + '\n')
        compiler = ['node', str(install / '@typescript/native-preview/bin/tsgo')]
        if run(compiler + ['--version'], cwd=work).strip() != 'Version ' + COMPILER:
            raise RuntimeError('Wrong compiler binary version')
        command = compiler + ['--pretty', 'false', '--noEmit', '-p', str(work / 'tsconfig.json')]
        discovered = run(command + ['--listFilesOnly'], cwd=work).splitlines()
        if any(str(work / name) not in discovered for name in config['files']):
            raise RuntimeError('Compiler discovery omitted a caller')
        diagnostics = run(command, cwd=work)
        retained = config['files'] + PRELUDE_FILES + ['prelude.ts', 'tsconfig.json', 'manifest.json']
        yield work, diagnostics, retained


def retain_inputs(work, output, names):
    """Retain the exact sources seen by the compiler, after the caller's runtime checks pass."""
    for name in names:
        target = output / 'compiled-inputs' / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(work / name, target)
