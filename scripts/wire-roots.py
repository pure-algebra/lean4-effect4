#!/usr/bin/env python3
"""Connect orphan library modules and batteries to their existing roots.

The axiom gate remains the authority for root separation. This repair adds imports only, and it
never imports a negative fixture.
"""
import argparse
import re
import sys
from pathlib import Path

from lib.lean_imports import imports_of, source_closure

ROOT = Path(__file__).resolve().parents[1]
ROOTS = ('src/Effect4.lean', 'src/Effect4/Laws.lean', 'Test/All.lean')


def module_name(path):
    return path.removeprefix('src/').removesuffix('.lean').replace('/', '.')


def plan(root):
    """Return the smallest acyclic set of orphan import roots, without writing files."""
    inventory = {p.relative_to(root).as_posix() for folder in ('src/Effect4', 'Test')
                 for p in (root / folder).rglob('*.lean')}
    inventory -= set(ROOTS)
    inventory = {p for p in inventory if not p.startswith('Test/fixtures/')}
    groups = {
        ROOTS[0]: {p for p in inventory if p.startswith('src/') and not p.startswith('src/Effect4/Laws/')},
        ROOTS[1]: {p for p in inventory if p.startswith('src/Effect4/Laws/')},
        ROOTS[2]: {p for p in inventory if p.startswith('Test/')},
    }
    result = {}
    for target, sources in groups.items():
        reached = set(source_closure(root, [target]))
        if target == ROOTS[0] and any(p.startswith('src/Effect4/Laws') for p in reached):
            raise ValueError('Effect4 reaches Laws; repair that import before wiring roots')
        missing = sources - reached
        imported = {m for path in missing for m in imports_of(root / path)}
        entries = sorted(path for path in missing if module_name(path) not in imported)
        covered = set(source_closure(root, entries)) if entries else set()
        if missing - covered:
            raise ValueError('orphan import cycle: ' + ', '.join(sorted(missing - covered)))
        if target == ROOTS[0] and any(p.startswith('src/Effect4/Laws') for p in covered):
            raise ValueError('an orphan core module reaches Laws; repair its import before wiring roots')
        if entries:
            result[target] = [module_name(path) for path in entries]
    return result


def wire(root, check=False):
    additions = plan(root)
    for target, modules in additions.items():
        print(f'{target}: ' + ', '.join(modules))
        if check:
            continue
        path = root / target
        text = path.read_text(encoding='utf-8')
        lines = text.splitlines(keepends=True)
        header = set(imports_of(path))
        positions = [i for i, line in enumerate(lines)
                     if re.match(r'^(?:public )?(?:meta )?import (?:all )?', line)
                     and line.strip().split()[-1] in header]
        if not positions:
            raise ValueError(f'no import header in {target}')
        at = positions[-1] + 1
        lines[at:at] = ['import ' + module + '\n' for module in modules]
        path.write_text(''.join(lines), encoding='utf-8', newline='\n')
    return bool(additions)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='report additions without writing them')
    args = parser.parse_args()
    changed = wire(ROOT, args.check)
    if not changed:
        print('PASS roots: every module is reached by its root')
    return 1 if changed and args.check else 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError) as error:
        print(f'wire-roots: {error}', file=sys.stderr)
        sys.exit(2)
