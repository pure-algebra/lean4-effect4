"""The pinned host the truth lanes run on: bun, the rc.112 install, and the link beside the harness.

Shared by `scripts/check-truth.py` (the hand-written corpus with its tapes) and
`scripts/check-corpus.py` (the generated corpus). One selection, one refusal set: the
install must carry `effect@4.0.0-rc.112` and its sqlite driver, `bun` must exist, and an
existing `harness/truth/node_modules` link must select the same install, because bun
resolves a generated module's `effect` import from the harness, not from the current
directory.

The compiler is the one compiler of decisions row 57, `@typescript/native-preview` (tsgo),
from the same install; it is run under node, whose pipe handle its client reads.

A second build since decisions row 248: the release, `effect@4.0.1`, for the release lane
(`scripts/check-truth-release.py`, `harness/truth/RELEASE-LANE.md`). `select` and its refusals
are the pin's and did not change. `release_install` and `select_release` accept the release
only where `EFFECT4_RELEASE_NODE_MODULES` names it: there is no default path, and nothing is
installed or downloaded. `RELEASE_ENTRY_POINTS` is the one table of the entry points that the
release moved.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

PINNED = '4.0.0-rc.112'
RELEASE = '4.0.1'
RELEASE_ENV = 'EFFECT4_RELEASE_NODE_MODULES'
DRIVER = '@effect/sql-sqlite-bun'

# The entry points by build: the pin's specifier on the left, the release's on the right
# (`vendor/effect-4.0.1/src` has no `unstable/` folder). The release lane rewrites the left
# column to the right one in its work copy of the harness sources, and nowhere else: the
# committed sources keep the pin's spelling until the pin lane ends (the migration plan's M8).
RELEASE_ENTRY_POINTS = {
    'effect/unstable/persistence': 'effect/persistence',
    'effect/unstable/reactivity/Reactivity': 'effect/reactivity/Reactivity',
    'effect/unstable/sql': 'effect/sql',
}


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


def release_install(environ=os.environ):
    """Return `(modules, driver)` for the release; exit with a FAIL line when it is not selected.

    The selection is explicit. `EFFECT4_RELEASE_NODE_MODULES` names a `node_modules` directory
    that holds `effect@4.0.1`; there is no default, and this function reads the file system only.
    `driver` says whether that directory also holds the release's sqlite driver. An install
    without the driver is accepted, and the lane then does not run the programs that need it.
    A driver of another version is refused: its `effect` imports would be another build's.
    """
    named = environ.get(RELEASE_ENV, '')
    if not named:
        sys.exit(f'FAIL truth-release: set {RELEASE_ENV} to a node_modules directory that holds '
                 f'effect@{RELEASE}; there is no default path, and nothing is downloaded')
    modules = Path(named).resolve()
    package = modules / 'effect/package.json'
    found = json.loads(package.read_text())['version'] if package.is_file() else None
    if found != RELEASE:
        sys.exit(f'FAIL truth-release: {RELEASE_ENV} must contain effect@{RELEASE} '
                 f'(found {"effect@" + found if found else "no effect package"} in {modules})')
    driver = modules / DRIVER / 'package.json'
    if not driver.is_file():
        return modules, False
    driver_version = json.loads(driver.read_text())['version']
    if driver_version != RELEASE:
        sys.exit(f'FAIL truth-release: {RELEASE_ENV} holds {DRIVER}@{driver_version}; '
                 f'the release lane accepts {DRIVER}@{RELEASE} or no driver')
    return modules, True


def compiler_version(modules: Path):
    """The version of the one compiler in an install, or `None` when the install has none."""
    package = modules / '@typescript/native-preview/package.json'
    if not package.is_file() or not (modules / '@typescript/native-preview/bin/tsgo').is_file():
        return None
    return json.loads(package.read_text())['version']


def pinned_compiler(root: Path):
    """The compiler version every typing lane runs: the one `ts/eff/package.json` pins."""
    return json.loads((root / 'ts/eff/package.json').read_text())['devDependencies']['@typescript/native-preview']


def compiler_refusal(modules: Path, pinned: str):
    """Why an install's compiler is refused, or `None`: it must be the pinned tsgo, by version."""
    found = compiler_version(modules)
    if found is None:
        return f'must contain @typescript/native-preview@{pinned} (the one compiler, tsgo)'
    if found != pinned:
        return f'holds @typescript/native-preview@{found}; the one compiler is @{pinned} (ts/eff/package.json)'
    return None


def select_release(root: Path, environ=os.environ):
    """Return `(bun, modules, host_path, driver)` for the release lane.

    `release_install` selects the build. This function adds the tools the host phase runs on:
    bun, and the pinned compiler with node, from the same install as in `select`. It does not
    read or write `harness/truth/node_modules`, which selects the pin: the release lane links
    the install inside its own work copy.
    """
    modules, driver = release_install(environ)
    refusal = compiler_refusal(modules, pinned_compiler(root))
    if refusal:
        sys.exit(f'FAIL truth-release: {RELEASE_ENV} {refusal}')
    if not shutil.which('node'):
        sys.exit("FAIL truth-release: node is required (the compiler's synchronous client reads its pipe handle)")
    bun = shutil.which('bun') or shutil.which('bun.exe')
    if not bun:
        sys.exit('FAIL truth-release: bun is required')

    def host_path(path):
        if os.name != 'nt' and bun.lower().endswith('.exe'):
            return subprocess.check_output(['wslpath', '-w', str(path)], text=True).strip()
        return str(path)

    return bun, modules, host_path, driver


def link_install(link: Path, modules: Path):
    """Make `link` select `modules`, the way `select` links the pin beside the harness."""
    if os.name == 'nt':
        script = "New-Item -ItemType Junction -Path $env:E4_TRUTH_LINK -Target $env:E4_TRUTH_MODULES | Out-Null"
        subprocess.run(['pwsh', '-NoProfile', '-Command', script], check=True,
                       env={**os.environ, 'E4_TRUTH_LINK': str(link), 'E4_TRUTH_MODULES': str(modules)})
    else:
        link.symlink_to(modules, target_is_directory=True)


def compiler(modules: Path):
    """The command that runs the one compiler's CLI over a project."""
    return [shutil.which('node') or 'node', str(modules / '@typescript/native-preview/bin/tsgo')]


def copy_prelude(source: Path, destination: Path):
    """Copy the runtime prelude and its sibling implementations for either truth lane."""
    for name in ['prelude.ts', 'prelude-atoms.gen.ts', 'records.ts', 'tuples.ts', 'control.ts']:
        shutil.copyfile(source / name, destination / name)
