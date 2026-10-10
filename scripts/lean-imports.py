#!/usr/bin/env python3
"""Print the workspace modules that the given Lean files import, one per line.

A recipe that runs `lake env lean --run FILE` builds exactly these first:
`lake build $(python3 scripts/lean-imports.py FILE)`. `lake env` builds nothing, and depending on
`build` (the whole battery) to get them built made every such gate pay for every module. A module
of the toolchain (`Lean`, `Std`, `Init`, `Lake`) needs no build and is left out.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCE_DIRS = [ROOT / 'src', ROOT / 'tools', ROOT]
IMPORT = re.compile(r'^\s*(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)', re.M)


def is_workspace(module: str) -> bool:
    relative = Path(*module.split('.')).with_suffix('.lean')
    return any((base / relative).is_file() for base in SOURCE_DIRS)


def imports(path: Path) -> list[str]:
    text = path.read_text(encoding='utf-8')
    # the header ends at the first command; a docstring or a declaration ends it soonest
    header = re.split(r'^\s*(?:/-|namespace|open|set_option|def|theorem|#)', text, maxsplit=1, flags=re.M)[0]
    return IMPORT.findall(header)


def main(argv: list[str]) -> int:
    if not argv:
        print('usage: lean-imports.py FILE...', file=sys.stderr)
        return 2
    seen: list[str] = []
    for name in argv:
        for module in imports(Path(name)):
            if module not in seen and is_workspace(module):
                seen.append(module)
    print(' '.join(seen))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
