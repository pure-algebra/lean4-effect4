"""The pinned host the truth lanes run on: bun, the rc.112 install, and the link beside the harness.

Shared by `scripts/check-truth.py` (the hand-written corpus with its tapes) and
`scripts/check-corpus.py` (the generated corpus). One selection, one refusal set: the
install must carry `effect@4.0.0-rc.112` and its sqlite driver, `bun` must exist, and an
existing `harness/truth/node_modules` link must select the same install, because bun
resolves a generated module's `effect` import from the harness, not from the current
directory.

The compiler is the one compiler of decisions row 57, `@typescript/native-preview` (tsgo),
from the same install; it is run under node, whose pipe handle its client reads.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

PINNED = '4.0.0-rc.112'


def select(root: Path, truth: Path):
    """Return `(bun, modules, host_path)`; exit with a FAIL line when the host is not the pin."""
    modules = Path(os.environ.get('EFFECT4_EFFECT_NODE_MODULES', root / 'ts/eff/node_modules')).resolve()
    package = modules / 'effect/package.json'
    if not package.is_file() or json.loads(package.read_text())['version'] != PINNED:
        sys.exit(f'FAIL truth: EFFECT4_EFFECT_NODE_MODULES must contain effect@{PINNED}')
    driver = modules / '@effect/sql-sqlite-bun/package.json'
    if not driver.is_file() or json.loads(driver.read_text())['version'] != PINNED:
        sys.exit(f'FAIL truth: EFFECT4_EFFECT_NODE_MODULES must contain @effect/sql-sqlite-bun@{PINNED} (bun install in ts/eff)')
    bun = shutil.which('bun') or shutil.which('bun.exe')
    if not bun:
        sys.exit('FAIL truth: bun is required')

    def host_path(path):
        if os.name != 'nt' and bun.lower().endswith('.exe'):
            return subprocess.check_output(['wslpath', '-w', str(path)], text=True).strip()
        return str(path)

    # The compiler is resolved from the same install, so one `bun install` serves every lane.
    if not (modules / '@typescript/native-preview/bin/tsgo').is_file():
        sys.exit('FAIL truth: EFFECT4_EFFECT_NODE_MODULES must contain @typescript/native-preview (bun install in ts/eff)')
    if not shutil.which('node'):
        sys.exit("FAIL truth: node is required (the compiler's synchronous client reads its pipe handle)")

    # Bun resolves imports relative to the runner. An existing link must select the same pin.
    link = truth / 'node_modules'
    if link.exists():
        if not (link / 'effect').samefile(modules / 'effect'):
            sys.exit('FAIL truth: harness/truth/node_modules selects a different installation; use its path or relink explicitly')
    elif os.name == 'nt':
        script = "New-Item -ItemType Junction -Path $env:E4_TRUTH_LINK -Target $env:E4_TRUTH_MODULES | Out-Null"
        subprocess.run(['pwsh', '-NoProfile', '-Command', script], check=True,
                       env={**os.environ, 'E4_TRUTH_LINK': str(link), 'E4_TRUTH_MODULES': str(modules)})
    else:
        link.symlink_to(modules, target_is_directory=True)
    return bun, modules, host_path


def compiler(modules: Path):
    """The command that runs the one compiler's CLI over a project."""
    return [shutil.which('node') or 'node', str(modules / '@typescript/native-preview/bin/tsgo')]
