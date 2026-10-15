#!/usr/bin/env python3
"""Make's content keys and shared passes. Commands and dependency order stay in Make.

key NAME --inputs FILE... writes .lake/check/NAME.key only when its identity changes.
run NAME -- COMMAND... reuses a shared pass or runs the selected Make recipe.
"""
import argparse
import re
import subprocess
import sys
from pathlib import Path

from lib.gate_cache import prepare, run
from lib.lean_imports import source_closure

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='action', required=True)
    key = commands.add_parser('key')
    key.add_argument('name')
    key.add_argument('--runtime', choices=['none', 'lean', 'ts', 'ocaml', 'all'], default='none')
    key.add_argument('--environment', nargs='*', default=[])
    key.add_argument('--inputs', nargs='+', required=True)
    key.add_argument('--lean', nargs='*', default=[], help='Lean entry files or workspace modules')
    execute = commands.add_parser('run')
    execute.add_argument('--force', action='store_true')
    execute.add_argument('name')
    execute.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if not re.fullmatch(r'[a-z0-9][a-z0-9-]*', args.name):
        parser.error('a check name uses lowercase letters, digits and hyphens')
    if args.action == 'key':
        inputs = args.inputs
        if args.lean:
            inputs = inputs + source_closure(ROOT, args.lean) + [
                'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'scripts/lib/lean_imports.py']
        prepare(ROOT, args.name, inputs, args.runtime, args.environment)
        return 0
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command:
        parser.error('run needs a command after --')
    return run(ROOT, args.name, command, args.force)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f'check cache: {error}', file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError) and error.stderr:
            print(error.stderr, file=sys.stderr)
        sys.exit(2)
