#!/usr/bin/env python3
"""The release lane: the truth harness's host phase on effect@4.0.1, judged by the build ledger.

    python3 scripts/check-truth-release.py              the lane (`make check-truth-release`)
    python3 scripts/check-truth-release.py --promote    write the ledger's entries and the record
                                                        of this host run (`make gen-truth-ledger`)
    python3 scripts/check-truth-release.py --self-test  the controls; no install and no host run

    --host-tests FILE...   after the other arguments: bun test files to run on both builds too.
                           The make targets name the pinned lane's own (`TRUTH_HOST_TESTS`).

Decisions row 248 moves the pin to 4.0.1 in increments. Until the last area moves, the machine
is checked against both builds, and `harness/truth/build-ledger.tsv` says what each program's
comparison with each build must give (`scripts/lib/truth_ledger.py` owns the file's grammar).
The lane note is `harness/truth/RELEASE-LANE.md`.

What the lane does, in order:

1. The control. The pin's install, through the same work copy the release gets, must reproduce
   the committed `result.json`, `result.md`, modules and tapes byte for byte, and type-check.
   A difference on the release is then a difference of the build, not of the copy (evidence
   word: reproduced).
2. The release. The same runner on `EFFECT4_RELEASE_NODE_MODULES` (`truth_host.select_release`:
   explicit, no default, no download; bun runs with `--no-install`). The manifest is the
   committed `harness/truth/corpus.json`: no second Lean run. The work copy holds the files
   that the runner and the sources of `harness/truth/tsconfig.json` reach by relative imports,
   with the moved entry points rewritten from the one table `truth_host.RELEASE_ENTRY_POINTS`;
   the committed sources are not touched. An install without the sqlite driver is accepted: a
   program whose module mentions the prelude's `Sql` is then not run, and the driver's import
   becomes a stub that dies if a program reaches it. The modules the release ran must be the
   committed ones, byte for byte, and must type-check against the release's declarations under
   the pinned compiler (the pinned lane's DI-49 refusal). The host controls that the pinned
   lane runs beside itself (`bun test`, the Makefile's `TRUTH_HOST_TESTS`) run on both work
   copies too, when the caller names them.
3. The comparison. Each program's entries on both builds against its ledger line. The pin's
   entries are read from the committed `result.json`, which step 1 has just reproduced. A
   program that leaves its line fails the lane with a finding that names the program, the
   build, the field and both values. A known difference in one field excuses no other field,
   and a missing observation is neither agreement nor disagreement: it is `not-run` or `n/a`,
   or the lane refuses the result. A tape that the release records differently fails the lane
   too: the manifest replays the committed tape, so that comparison would be void.

Each host run keeps what it ran on: the build, the runtime, the compiler, and the digests of
the manifest, the modules and the tapes. `harness/truth/build-ledger.run.json` is the committed
record of the host run that wrote the ledger, and the lane refuses a run on anything else, as
the pinned lane refuses a drifted `result.json` (evidence word: reproduced). `--promote`
writes both files. The whole record, with the installs' paths, is
`.lake/truth-release/run.json`. The work copies stay beside it: the runner's own table is
`.lake/truth-release/release/harness/truth/result.md`, and `observed.tsv` is the ledger as
this host run would write it.

Evidence word: tested (a finite host run and a finite compiler run over the truth manifest).
The lane does not run the generated corpus, and it proves nothing.
"""
import hashlib
import json
import os
from pathlib import Path
import posixpath
import re
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(root / 'scripts/lib'))
import truth_host  # noqa: E402
import truth_ledger  # noqa: E402

truth = root / 'harness/truth'
LEDGER = truth / 'build-ledger.tsv'
RECORD = truth / 'build-ledger.run.json'
WORK = root / '.lake/truth-release'
RUNNER = 'harness/truth/run-truth.ts'
HERE = posixpath.dirname(RUNNER)
# The one directory of the compiler configuration's `include` that the runner fills.
OUTPUT = 'generated'
BUILDS = (truth_host.PINNED, truth_host.RELEASE)
STUB = 'sqlite-driver-absent.ts'
STUB_MARK = 'effect4 truth-release: the selected install has no ' + truth_host.DRIVER
STUB_TEXT = f'''// WRITTEN by scripts/check-truth-release.py; never committed.
// The selected install has no {truth_host.DRIVER}. The lane does not run a program whose
// module mentions the prelude's `Sql`; a program that reaches this stub anyway dies here, and
// the lane fails on the mark below. The types are the two members `prelude.ts` names.
import {{ Effect }} from "effect"
export declare namespace SqliteClient {{
  export interface SqliteClient {{
    readonly unsafe: (text: string, params: ReadonlyArray<unknown>) => Effect.Effect<ReadonlyArray<unknown>, unknown>
  }}
}}
export const SqliteClient = {{
  make: (_options: {{ readonly filename: string; readonly disableWAL: boolean }}): Effect.Effect<SqliteClient.SqliteClient> =>
    Effect.die(new Error("{STUB_MARK}"))
}}
'''
PROBE_TEXT = '''// WRITTEN by scripts/check-truth-release.py; never committed.
// Where `effect` resolves from each directory that holds a source of this work copy.
const dirs = process.argv.slice(2)
console.log(JSON.stringify(Object.fromEntries(dirs.map((dir) => [dir, Bun.resolveSync("effect", dir)]))))
'''


class LaneError(Exception):
    """A refusal of the lane, as the text after `FAIL truth-release: `."""


# ---- the pure part: imports, entry points, the driver test, the comparison --------------------

# A static import or re-export and its specifier. The clause between the keyword and `from`
# holds names, braces, commas and `*` only, so a declaration such as `export const x = "s"`
# is not read as one. A dynamic `import(...)` is not followed: the runner's are the generated
# modules, which it writes itself.
IMPORT = re.compile(r'''(?m)^(?P<head>[ \t]*(?:import|export)\b(?:[\w\s{},*$]*?\bfrom)?\s*)'''
                    r'''(?P<quote>['"])(?P<spec>[^'"\n]+)(?P=quote)''')


def specifiers(text):
    return [found['spec'] for found in IMPORT.finditer(text)]


def rewrite(text, table):
    """`(text with each specifier of the table replaced, the pairs replaced in order)`."""
    done = []

    def swap(found):
        spec = found['spec']
        if spec not in table:
            return found[0]
        done.append((spec, table[spec]))
        return found['head'] + found['quote'] + table[spec] + found['quote']

    return IMPORT.sub(swap, text), done


def closure(read, entries):
    """The files `entries` reach by static relative imports, the entries first, as repository
    paths. `read(path)` gives a file's text, or `None` for a path that is no file of the
    repository."""
    seen, queue = [], list(entries)
    while queue:
        path = queue.pop(0)
        if path in seen:
            continue
        text = read(path)
        if text is None:
            raise LaneError(f'{path} is no file of the repository')
        seen.append(path)
        for spec in specifiers(text):
            if not spec.startswith('.'):
                continue
            target = posixpath.normpath(posixpath.join(posixpath.dirname(path), spec))
            if target.startswith('..') or read(target) is None:
                raise LaneError(f'{path} imports {spec}, which is no file of the repository')
            queue.append(target)
    return seen


def export_target(exports, subpath):
    """The file a package's `exports` gives a subpath (`.` or `./x/y`), or `None`: an exact key,
    else the pattern with the longest prefix, the longer key on a tie, as Node orders them."""
    if subpath in exports:
        target = exports[subpath]
    else:
        best = None
        for key, value in exports.items():
            if key.count('*') != 1:
                continue
            prefix, suffix = key.split('*')
            if subpath.startswith(prefix) and subpath.endswith(suffix) and len(subpath) >= len(key) - 1:
                rank = (len(prefix), len(key))
                if best is None or rank > best[0]:
                    best = (rank, value, subpath[len(prefix):len(subpath) - len(suffix)])
        if best is None:
            return None
        target = best[1].replace('*', best[2]) if isinstance(best[1], str) else best[1]
    if isinstance(target, dict):
        target = target.get('import', target.get('default'))
    return target if isinstance(target, str) else None


def unresolved(spec, exports, is_file, driver):
    """Why a bare specifier of the work copy is refused, or `None` when the lane accepts it:
    a builtin, a path of the selected `effect` that its `exports` give and that exists, or the
    driver when the install holds it."""
    if spec.startswith(('node:', 'bun:')):
        return None
    if spec == 'effect' or spec.startswith('effect/'):
        target = export_target(exports, '.' + spec[len('effect'):])
        if target is None:
            return 'the selected effect does not export it, and the entry-point table does not map it'
        return None if is_file(target) else f'the selected effect exports it as {target}, which is no file'
    if driver and (spec == truth_host.DRIVER or spec.startswith(truth_host.DRIVER + '/')):
        return None
    return 'not a path of effect, not a builtin, and not a driver of the selected install'


def needs_driver(program):
    """Whether a program's printed module mentions the prelude's `Sql`, the one export that
    reaches the sqlite driver (`Sql.open` builds the client)."""
    return re.search(r'\bSql\.', program['decl'] or program['expr'] or '') is not None


def carry(builds, lines, programs, observed):
    """The ledger a host run would write: the observed entries, with `reason` and `slice` kept
    from the lines that still need them and emptied on the lines whose six entries are `yes`."""
    out = {}
    for name in programs:
        entries = {(build, field): observed[build][name][field]
                   for build in builds for field in truth_ledger.FIELDS}
        line = {'entries': entries, 'reason': '', 'slice': ''}
        if name in lines and not truth_ledger.all_yes(line, builds):
            line['reason'], line['slice'] = lines[name]['reason'], lines[name]['slice']
        out[name] = line
    return list(programs), out


def judge_runs(builds, manifest, results, skipped, ledger_text):
    """The lane's comparison of two runner results with the ledger: `(findings, observed, lines)`. Pure.

    `results[build]` is the runner's result on that build and `skipped[build]` the programs
    the lane did not select there. `findings` holds the ledger's own defects, then one finding
    for each entry that leaves its line. Every program of the manifest is observed on both
    builds or the result is refused (`truth_ledger.Inconsistent`): a missing result is never
    read as agreement.
    """
    programs = [program['name'] for program in manifest['programs']]
    observed = {build: truth_ledger.observe(manifest, results[build], not_run=skipped.get(build, ()))
                for build in builds}
    if ledger_text is None:
        return ['the ledger is missing; `make gen-truth-ledger` writes it'], observed, {}
    try:
        order, lines, findings = truth_ledger.parse(ledger_text, builds)
    except truth_ledger.Unreadable as refusal:
        return [f'the ledger is not read: {refusal}'], observed, {}
    return findings + truth_ledger.judge(builds, order, lines, programs, observed), observed, lines


def unpromotable(ledger_text, lines):
    """Why a promote must not overwrite the ledger on disk, or `None`. The hand columns are
    carried from the lines that were read, so a line that was not read would lose its reason
    and its slice."""
    if ledger_text is None:
        return None
    written = [text for text in ledger_text.split('\n') if text and not text.startswith('#')][1:]
    if len(written) == len(lines):
        return None
    return (f'the ledger on disk has {len(written)} line(s) and {len(lines)} could be read; repair or '
            f'remove it first, or its hand columns are lost')


def same_as_committed(ran, build, modules, kept_modules, tapes, kept_tapes):
    """The modules and tapes of one run against the committed ones, each set as name to bytes.

    Returns `(moved, tape findings)`. `moved` names each module that is not the committed
    module byte for byte, and each difference between the modules written and the programs
    that ran. A tape finding names a program that ran whose tape is not the committed tape,
    and a tape recorded for a program that did not run. The pin's lane holds the committed
    sets to a fresh run, so they are the identity of what a build ran."""
    expected = {f'{program["name"]}.ts' for program in ran
                if program['decl'] is not None or program['expr'] is not None}
    moved = [f'{OUTPUT}/{name}' for name in sorted(set(modules) ^ expected)]
    moved += [f'{OUTPUT}/{name}' for name in sorted(set(modules) & expected)
              if kept_modules.get(name) != modules[name]]
    findings = []
    names = {program['name'] for program in ran}
    for name in sorted(set(tapes) - {f'{n}.jsonl' for n in names}):
        findings.append(f'{name}: {build} tape: recorded for a program the lane did not run')
    for name in sorted(names):
        fresh, kept = tapes.get(f'{name}.jsonl'), kept_tapes.get(f'{name}.jsonl')
        if (fresh is None) != (kept is None):
            findings.append(f'{name}: {build} tape: {"recorded" if fresh is not None else "not recorded"} on '
                            f'this build, {"committed" if kept is not None else "not committed"} for the pin')
        elif fresh is not None and fresh != kept:
            findings.append(f'{name}: {build} tape: the build answered a host row differently from '
                            f'{HERE}/tapes/{name}.jsonl, which the manifest replays')
    return moved, findings


def tests_passed(status, said):
    """How many tests a `bun test` run passed, as text, or `None` when the run is refused: a
    nonzero exit status, a failed test, no count, or no test at all."""
    passed = re.search(r'^\s*(\d+) pass$', said, re.M)
    failed = re.search(r'^\s*(\d+) fail$', said, re.M)
    if status != 0 or passed is None or passed[1] == '0' or failed is None or failed[1] != '0':
        return None
    return passed[1]


def digest(files):
    """The SHA-256 of a set of files: each name and its bytes, in name order."""
    sha = hashlib.sha256()
    for name, data in sorted(files.items()):
        sha.update(name.encode() + b'\0' + data + b'\0')
    return sha.hexdigest()


def differences(recorded, seen, path=''):
    """Where two JSON values differ: one line for each leaf, with its path and both values."""
    if isinstance(recorded, dict) and isinstance(seen, dict):
        found = []
        for key in sorted(set(recorded) | set(seen)):
            where = f'{path}.{key}' if path else key
            if key not in recorded or key not in seen:
                found.append(f'{where}: {"recorded" if key in recorded else "this run"} only')
            else:
                found.extend(differences(recorded[key], seen[key], where))
        return found
    if recorded != seen:
        return [f'{path}: recorded {json.dumps(recorded)}, this run {json.dumps(seen)}']
    return []


def record_findings(kept, text):
    """The findings of the committed record against this host run's: `text` is the committed
    file, or `None`. The ledger's entries were measured on what the record names, so a host
    run on anything else is refused."""
    name = f'{HERE}/build-ledger.run.json'
    if text is None:
        return [f'{name} is missing; `make gen-truth-ledger` writes it']
    try:
        recorded = json.loads(text)
    except ValueError as error:
        return [f'{name} is not JSON: {error}']
    return [f'{name}: {line}; `make gen-truth-ledger` writes the record of this host run'
            for line in differences(recorded, kept)]


# ---- the I/O part -----------------------------------------------------------------------------

def text_of(file):
    """A file's text, by its bytes: UTF-8 on every host, with its line ends as they are."""
    return file.read_bytes().decode('utf-8')


def write(file, text):
    file.write_bytes(text.encode('utf-8'))


def read_repository(path):
    file = root / path
    return text_of(file) if file.is_file() else None


def type_roots():
    """The sources the committed compiler configuration names, as repository paths: every
    file its `include` matches beside the runner. The runner's output directory is filled by
    the run. A pattern that matches no file is refused: no lane would compile what it names."""
    roots = []
    for pattern in json.loads(text_of(truth / 'tsconfig.json'))['include']:
        if pattern == OUTPUT:
            continue
        if (truth / pattern).is_dir():
            raise LaneError(f'{HERE}/tsconfig.json includes the directory "{pattern}"; the lane copies the files '
                            f'it names and leaves `{OUTPUT}` to the runner')
        found = sorted(file for file in truth.glob(pattern) if file.is_file())
        if not found:
            raise LaneError(f'{HERE}/tsconfig.json includes "{pattern}", which matches no file')
        roots.extend(file.relative_to(root).as_posix() for file in found)
    return roots


def build_work_copy(work, modules, table, driver, extra=()):
    """The work copy for one build: the import closure of the runner, of the type-checked
    sources and of the `extra` sources, in the repository's layout; the compiler options
    beside each source; and the install linked where the pinned layout has it. Returns
    `(files, rewrites)`; refuses a specifier it cannot place."""
    if work.exists():
        shutil.rmtree(work)
    files = closure(read_repository, [RUNNER] + type_roots() + list(extra))
    table = dict(table)
    if not driver:
        table[truth_host.DRIVER] = './' + STUB
    rewrites = []
    for path in files:
        text, done = rewrite(read_repository(path), table)
        target = work / path
        target.parent.mkdir(parents=True, exist_ok=True)
        if done:
            write(target, text)
            rewrites.extend((path, old, new) for old, new in done)
            if any(old == truth_host.DRIVER for old, _ in done):
                write(target.parent / STUB, STUB_TEXT)
        else:
            shutil.copyfile(root / path, target)
    for directory in sorted({posixpath.dirname(path) for path in files}):
        if (root / directory / 'tsconfig.json').is_file():
            shutil.copyfile(root / directory / 'tsconfig.json', work / directory / 'tsconfig.json')
    # `effect` resolves upward from every source to the link at the top; the runner also reads
    # the version from the link beside itself.
    truth_host.link_install(work / 'node_modules', modules)
    truth_host.link_install(work / HERE / 'node_modules', modules)

    package = modules / 'effect'
    exports = json.loads(text_of(package / 'package.json'))['exports']
    refused = []
    for path in files:
        for spec in specifiers(text_of(work / path)):
            if spec.startswith('.'):
                continue
            why = unresolved(spec, exports, lambda target: (package / target).is_file(), driver)
            if why:
                refused.append(f'{path} imports "{spec}": {why}')
    if refused:
        raise LaneError('; '.join(refused))
    return files, rewrites


def entry_point_findings(installs):
    """Each pair of `truth_host.RELEASE_ENTRY_POINTS` against the two installs: the pin exports
    the left spelling and not the right, the release the right and not the left. `installs`
    maps a build to `(node_modules, whether it is the pin)`. A pair that no copied source
    imports is checked here too."""
    found = []
    for build, (modules, is_pin) in installs.items():
        package = modules / 'effect'
        exports = json.loads(text_of(package / 'package.json'))['exports']
        for old, new in truth_host.RELEASE_ENTRY_POINTS.items():
            for spec, wanted in ((old, is_pin), (new, not is_pin)):
                resolves = unresolved(spec, exports, lambda target: (package / target).is_file(), False) is None
                if resolves != wanted:
                    found.append(f'effect@{build} {"exports" if resolves else "does not export"} "{spec}"')
    return found


def source_directories(work):
    found = set()
    for directory, names, files in os.walk(work):
        names[:] = [name for name in names if name != 'node_modules']
        if any(file.endswith('.ts') for file in files):
            found.add(directory)
    return sorted(found)


def host_run(bun, host_path, work, modules, manifest_bytes):
    """The runner on one work copy. Returns its result; refuses a run that did not complete,
    and a work copy any directory of which resolves `effect` outside the selected install."""
    here = work / HERE
    (here / 'corpus.json').write_bytes(manifest_bytes)
    ran = subprocess.run([bun, '--no-install', 'run', host_path(work / RUNNER),
                          '--manifest', host_path(here / 'corpus.json'), '--out', host_path(here),
                          '--timeout', '300', '--tape-out', host_path(here / 'tapes')],
                         cwd=work, text=True, encoding='utf-8', capture_output=True, timeout=180)
    write(work / 'runner.stdout', ran.stdout)
    write(work / 'runner.stderr', ran.stderr)
    # 0: the runner's own rule holds; 1: it names disagreements, which the ledger judges.
    if ran.returncode not in (0, 1) or not (here / 'result.json').is_file():
        raise LaneError(f'the runner did not complete in {work.relative_to(root)} (exit {ran.returncode}):\n'
                        f'{ran.stdout[-2000:]}{ran.stderr[-2000:]}')
    result = json.loads(text_of(here / 'result.json'))

    write(work / 'resolve-probe.ts', PROBE_TEXT)
    probed = subprocess.run([bun, '--no-install', 'run', host_path(work / 'resolve-probe.ts')]
                            + [host_path(directory) for directory in source_directories(work)],
                            cwd=work, text=True, encoding='utf-8', capture_output=True, timeout=60)
    if probed.returncode != 0:
        raise LaneError(f'the resolution probe failed in {work.relative_to(root)}:\n{probed.stdout}{probed.stderr}')
    selected = (modules / 'effect').resolve()
    for directory, resolved in json.loads(probed.stdout).items():
        if selected not in Path(resolved).resolve().parents:
            raise LaneError(f'{directory} resolves effect to {resolved}, outside the selected install {selected}')
    version = json.loads(text_of(selected / 'package.json'))['version']
    if result['effect'] != version:
        raise LaneError(f'the runner reports effect {result["effect"]}, the selected install is {version}')
    return result


def host_tests(bun, host_path, work, tests):
    """The pinned lane's host controls on one work copy: `bun test` over the named files.
    Returns the tests' own count line; refuses a failing or an empty run."""
    ran = subprocess.run([bun, '--no-install', 'test'] + [host_path(work / test) for test in tests],
                         cwd=work, text=True, encoding='utf-8', capture_output=True, timeout=300)
    said = ran.stdout + ran.stderr
    write(work / 'host-tests.txt', said)
    passed = tests_passed(ran.returncode, said)
    if passed is None:
        raise LaneError(f'the host tests failed in {work.relative_to(root)} (exit {ran.returncode}):\n{said[-3000:]}')
    return f'{passed} pass in {len(tests)} file(s)'


def type_check(modules, host_path, work):
    """The pinned lane's DI-49 refusal on one work copy: the modules the build just ran, the
    prelude, the runner and the session sources under the pinned compiler, against the selected
    install's declarations. Returns `(compiler version, sources compiled)`; refuses a
    diagnostic, and a declaration of `effect` read from any other install."""
    here = work / HERE
    compiler = truth_host.compiler(modules)
    said = subprocess.run(compiler + ['--version'], text=True, encoding='utf-8', capture_output=True, timeout=60)
    version = said.stdout.strip().removeprefix('Version').strip()
    if said.returncode != 0 or version != truth_host.compiler_version(modules):
        raise LaneError(f'the compiler of {modules} says "{said.stdout.strip()}{said.stderr.strip()}", '
                        f'its package says {truth_host.compiler_version(modules)}')
    command = compiler + ['--pretty', 'false', '--noEmit', '-p', host_path(here / 'tsconfig.json')]
    typed = subprocess.run(command, cwd=here, text=True, encoding='utf-8', capture_output=True, timeout=300)
    selected = (modules / 'effect').resolve()
    effect = json.loads(text_of(selected / 'package.json'))['version']
    if typed.returncode != 0:
        raise LaneError(f'{here.relative_to(root)} does not type-check against effect@{effect} under '
                        f'tsgo {version}:\n{typed.stdout}{typed.stderr}')
    listed = subprocess.run(command + ['--listFilesOnly'], cwd=here, text=True, encoding='utf-8',
                            capture_output=True, timeout=300)
    files = [Path(line.strip()).resolve() for line in listed.stdout.splitlines() if line.strip()]
    owners = {}

    def owner(file):
        for directory in file.parents:
            if directory not in owners:
                package = directory / 'package.json'
                owners[directory] = (json.loads(text_of(package)).get('name'), directory) if package.is_file() else None
            if owners[directory] is not None:
                return owners[directory]
        return (None, None)

    inside = work.resolve()
    sources = [file for file in files if inside in file.parents]
    foreign = [file for file in files if inside not in file.parents and owner(file)[0] == 'effect'
               and owner(file)[1] != selected]
    if listed.returncode != 0 or foreign or not any(selected in file.parents for file in files):
        raise LaneError(f'the type check of {here.relative_to(root)} did not read effect@{effect} alone: '
                        f'{len(foreign)} declaration(s) of another effect, first {foreign[:1]}; '
                        f'exit {listed.returncode}')
    return version, len(sources)


def identity(here, ran, build):
    """The modules and tapes of one run against the committed ones: `same_as_committed` over
    the files of the work copy and of `harness/truth`. Returns the two fresh sets too."""
    def files(folder, pattern):
        return {file.name: file.read_bytes() for file in folder.glob(pattern)} if folder.is_dir() else {}

    modules, tapes = files(here / OUTPUT, '*.ts'), files(here / 'tapes', '*')
    moved, findings = same_as_committed(ran, build, modules, files(truth / OUTPUT, '*.ts'),
                                        tapes, files(truth / 'tapes', '*'))
    return modules, tapes, moved, findings


def run_build(role, bun, host_path, modules, table, driver, manifest, manifest_bytes, tests):
    """One build end to end: the work copy, the runner, the compiler, the host tests, the
    identity of what ran. Returns the run's record, with its result and its tape findings under
    `_result`, `_tapes`."""
    work = WORK / role
    skipped = [] if driver else [program['name'] for program in manifest['programs'] if needs_driver(program)]
    ran = [program for program in manifest['programs'] if program['name'] not in skipped]
    files, rewrites = build_work_copy(work, modules, table, driver, tests)
    # The record names each rewritten specifier once, among the sources every run copies: it
    # does not depend on which host tests the caller names.
    always = set(closure(read_repository, [RUNNER] + type_roots()))
    moved_imports = sorted({(old, new) for path, old, new in rewrites if path in always})
    # The runner gets the committed manifest, or the same manifest without the programs not run.
    given = manifest_bytes if not skipped else (json.dumps(dict(manifest, programs=ran), indent=1) + '\n').encode()
    result = host_run(bun, host_path, work, modules, given)
    reached = [row['program'] for row in result['rows'] if STUB_MARK in json.dumps(row)]
    if reached:
        raise LaneError(f'{", ".join(reached)}: the program reached the absent {truth_host.DRIVER}; '
                        f'`needs_driver` did not select it')
    compiler, compiled = type_check(modules, host_path, work)
    tested = host_tests(bun, host_path, work, tests) if tests else None
    generated, tapes, moved, tape_findings = identity(work / HERE, ran, result['effect'])
    if moved:
        raise LaneError(f'{work.relative_to(root)}: the run did not use the committed modules: {", ".join(moved)}')
    return {
        # what the run ran on: the committed record's fields
        'effect': result['effect'],
        'driver': f'{truth_host.DRIVER}@{result["effect"]}' if driver else None,
        'runtime': {'bun': result['bun'], 'deadlineMs': result['timeoutMs']},
        'compiler': {'package': '@typescript/native-preview', 'version': compiler},
        'programs': {'ran': len(result['rows']), 'notRun': skipped},
        'modules': {'count': len(generated), 'sha256': digest(generated)},
        'tapes': {'count': len(tapes), 'sha256': digest(tapes)},
        'imports': [list(pair) for pair in moved_imports],
        # and what only this machine's run has
        '_local': {'role': role, 'install': str(modules), 'work': work.relative_to(root).as_posix(),
                   'sourcesCopied': len(files), 'sourcesCompiled': compiled, 'diagnostics': 0,
                   'hostTests': tested, 'rewrites': [list(item) for item in rewrites],
                   'modulesAre': f'each {HERE}/{OUTPUT}/<name>.ts byte for byte'},
        '_result': result, '_tapes': tape_findings,
    }


def lane(promote, tests):
    pin, release = BUILDS
    manifest_bytes = (truth / 'corpus.json').read_bytes()
    manifest = json.loads(manifest_bytes)
    programs = [program['name'] for program in manifest['programs']]
    bun, pin_modules, host_path = truth_host.select(root, truth)
    bun, modules, host_path, driver = truth_host.select_release(root)
    wrong = entry_point_findings({pin: (pin_modules, True), release: (modules, False)})
    if wrong:
        raise LaneError('the entry-point table `truth_host.RELEASE_ENTRY_POINTS` is not true of the two '
                        'installs: ' + '; '.join(wrong))

    # 1. the control: the pin through the work copy
    control = run_build('pin', bun, host_path, pin_modules, {}, True, manifest, manifest_bytes, tests)
    committed, local = control.pop('_result'), {pin: control.pop('_local')}
    here = WORK / 'pin' / HERE
    moved = [name for name in ('result.json', 'result.md') if (here / name).read_bytes() != (truth / name).read_bytes()]
    moved += control.pop('_tapes')
    if local[pin]['rewrites'] or moved:
        raise LaneError(f'the control failed: the work copy on effect@{pin} does not reproduce the committed '
                        f'artifacts ({"; ".join(moved) or local[pin]["rewrites"]}); run `make check-truth` first, '
                        f'then read {local[pin]["work"]}')
    print(f'truth-release: the control: effect@{pin} through the work copy ({local[pin]["sourcesCopied"]} '
          f'sources) reproduces result.json, result.md, {control["modules"]["count"]} modules and '
          f'{control["tapes"]["count"]} tapes byte for byte')

    # 2. the release
    record = run_build('release', bun, host_path, modules, truth_host.RELEASE_ENTRY_POINTS, driver,
                       manifest, manifest_bytes, tests)
    result, tape_findings, local[release] = record.pop('_result'), record.pop('_tapes'), record.pop('_local')
    skipped = record['programs']['notRun']
    print(f'truth-release: the release: effect@{record["effect"]}, {record["programs"]["ran"]} of '
          f'{len(programs)} programs run'
          + (f'; not run, the install has no {truth_host.DRIVER}: {", ".join(skipped)}' if skipped else ''))
    for path, old, new in local[release]['rewrites']:
        print(f'truth-release: the work copy of {path} imports "{new}" for "{old}"')
    for build, run in ((pin, control), (release, record)):
        print(f'truth-release: effect@{build} ran on bun {run["runtime"]["bun"]}; tsgo '
              f'{run["compiler"]["version"]} type-checks its {local[build]["sourcesCompiled"]} sources; '
              f'modules: {run["modules"]["count"]}, sha256 {run["modules"]["sha256"][:16]}; '
              f'tapes: {run["tapes"]["count"]}, sha256 {run["tapes"]["sha256"][:16]}; host tests: '
              + (local[build]['hostTests'] or 'none named'))

    # 3. the comparison: the record of what the host run ran on, then the entries
    kept = {
        'format': 'effect4-truth-release-run-v1',
        'generated': 'GENERATED by scripts/check-truth-release.py --promote; do not edit',
        'manifest': {'path': f'{HERE}/corpus.json', 'sha256': hashlib.sha256(manifest_bytes).hexdigest(),
                     'programs': len(programs)},
        'builds': {pin: control, release: record},
    }
    kept_text = json.dumps(kept, indent=2) + '\n'
    ledger_text = text_of(LEDGER) if LEDGER.is_file() else None
    findings, observed, lines = judge_runs(BUILDS, manifest, {pin: committed, release: result},
                                           {release: skipped}, ledger_text)
    findings = record_findings(kept, text_of(RECORD) if RECORD.is_file() else None) + findings + tape_findings
    fresh_order, fresh_lines = carry(BUILDS, lines, programs, observed)
    fresh = truth_ledger.render(BUILDS, fresh_order, fresh_lines)
    WORK.mkdir(parents=True, exist_ok=True)
    write(WORK / 'observed.tsv', fresh)
    write(WORK / 'run.json', json.dumps(dict(kept, local=local, findings=findings), indent=2) + '\n')

    if promote:
        refusal = unpromotable(ledger_text, lines)
        if refusal:
            raise LaneError(refusal)
        write(LEDGER, fresh)
        write(RECORD, kept_text)
        print(f'promoted {LEDGER.relative_to(root)} and {RECORD.relative_to(root)}')
        _, _, owed = truth_ledger.parse(fresh, BUILDS)
        for finding in owed + tape_findings:
            print(f'FAIL truth-release: {finding}')
        return 1 if owed or tape_findings else 0

    if findings:
        for finding in findings:
            print(f'FAIL truth-release: {finding}')
        print(f'truth-release: {len(findings)} finding(s); compare {LEDGER.relative_to(root)} with '
              f'{(WORK / "observed.tsv").relative_to(root)}, and read the runner\'s table in '
              f'{(WORK / "release" / HERE / "result.md").relative_to(root)}')
        return 1
    for text in truth_ledger.known(BUILDS, fresh_order, lines):
        print(f'truth-release: expected: {text}')
    count = truth_ledger.classes(BUILDS, fresh_order, lines)
    print(f'PASS truth-release: {len(programs)} programs match {LEDGER.relative_to(root)}: '
          f'{count["both"]} agree with both builds, {count["pin only"]} with effect@{pin} only '
          f'({count["not run"]} not run on effect@{release}), {count["release only"]} with '
          f'effect@{release} only, {count["neither"]} with neither')
    return 0


# ---- the controls -----------------------------------------------------------------------------

def self_test():
    """The controls, each with what it must give. No install is read and no host runs: the
    observation and the comparison on a small manifest of this function, the ledger's grammar,
    the run record, the import rewrite, the export resolution, the driver test, and the
    selection on scratch installs."""
    pin, release = BUILDS
    L = truth_ledger
    outcomes = []

    def control(name, ok, said=''):
        outcomes.append(bool(ok))
        print(f'--- control {name}: {"ok" if ok else "WRONG"}{": " + str(said) if said and not ok else ""}')

    def raises(action, *kinds):
        try:
            action()
        except kinds as error:
            return str(error) or type(error).__name__
        return ''

    def red(name, found, *reasons, absent=()):
        """A red control: every reason is in some finding, and no finding holds an `absent` text."""
        ok = all(any(reason in f for f in found) for reason in reasons) and not any(
            text in f for f in found for text in absent)
        control('red: ' + name, bool(found) and ok, ' | '.join(found) or 'no finding')

    forks = ['started 0', 'forked 0 1', 'started 1', 'exited 1 success', 'scheduled 0 0', 'exited 0 success']
    plain = ['started 0', 'exited 0 success']

    def program(name, schedule, decl='export const main = Effect.succeed(1)\n'):
        return {'name': name, 'decl': decl, 'expr': None, 'run': {'schedule': schedule},
                'runSync': {'exit': {'success': 1}}}

    # pA agrees everywhere. pB has one known difference, its schedule on the release. pC needs
    # the driver and is not run on the release. pD is the signed divergence of the pin.
    manifest = {'programs': [
        program('pA', plain), program('pB', forks),
        program('pC', plain, 'export const main = Effect.scoped(Sql.open(":memory:"))\n'),
        program('pD', ['started 0', 'exited 0 interrupt'])]}
    by_name = {item['name']: item for item in manifest['programs']}
    names = list(by_name)

    def report(name, schedule=None, **fields):
        """A runner result for one program that agrees on every field, with the given fields replaced."""
        own = by_name[name]['run']['schedule'] if schedule is None else schedule
        made = {'program': name, 'leanExit': 'success 1', 'hostExit': 'success 1', 'exitAgree': True,
                'scheduleAgree': own == by_name[name]['run']['schedule'], 'runSyncAgree': True,
                'host': {'schedule': own}, 'hostSync': {'exit': {'success': 1}}}
        made.update(fields)
        return made

    d_pin = report('pD', ['started 0', 'exited 0 fail'], exitAgree=False,
                   leanExit='interrupt [{"interrupt":0}]', hostExit='fail [{"fail":42}]')
    b_release = report('pB', ['started 0', 'exited 0 success'])
    on_pin = [report('pA'), report('pB'), report('pC'), d_pin]
    on_release = [report('pA'), b_release, report('pD')]
    skipped = {release: ['pC']}

    def judged(ledger, release_reports=None, pin_reports=None, skip=skipped):
        return judge_runs(BUILDS, manifest, {pin: {'rows': pin_reports or on_pin},
                                             release: {'rows': release_reports or on_release}}, skip, ledger)

    _, observed, _ = judged(None)

    # the observation
    control('an agreeing program is three `yes`', observed[pin]['pA'] == dict.fromkeys(L.FIELDS, L.YES))
    control('a schedule difference is the exact edit, without the `scheduled` rows',
            observed[release]['pB'] == {
                'exit': L.YES, 'sync': L.YES,
                'schedule': 'no: the host lacks machine rows 1-3 (forked 0 1, started 1, exited 1 success)'},
            observed[release]['pB'])
    control('an exit difference carries both exits',
            observed[pin]['pD'] == {
                'exit': 'no: machine interrupt [{"interrupt":0}], host fail [{"fail":42}]',
                'schedule': 'no: machine row 1 (exited 0 interrupt) is host row 1 (exited 0 fail)',
                'sync': L.YES}, observed[pin]['pD'])
    control('a program the lane did not select is three `not-run`',
            observed[release]['pC'] == dict.fromkeys(L.FIELDS, L.NOT_RUN))
    sync = L.entries_of(by_name['pA'], report('pA', runSyncAgree=False, hostSync={
        'exit': {'failure': {'reasons': [{'die': 'asyncFiber'}]}}}))['sync']
    control('a sync difference carries both sync exits',
            sync == 'no: machine success 1, host die [{"die":"asyncFiber"}]', sync)
    control('a module that does not load has no path in its entry',
            L.entries_of(by_name['pA'], report('pA', exitAgree=False, scheduleAgree=None, runSyncAgree=None,
                                               hostExit='module failed to load: Error: /work/x.ts')) ==
            {'exit': 'no: the module failed to load', 'schedule': L.NA, 'sync': L.NA})
    control('red: a schedule verdict that the compared schedules contradict is refused',
            'the runner says the schedules differ' in raises(
                lambda: L.entries_of(by_name['pA'], report('pA', scheduleAgree=False)), L.Inconsistent))
    control('red: a schedule verdict without the host schedule is refused',
            'pA: the runner gives a schedule verdict and no host schedule' in raises(
                lambda: L.entries_of(by_name['pA'], report('pA', host=None)), L.Inconsistent))

    # the ledger: the green control
    order, lines = carry(BUILDS, {}, names, observed)
    lines['pB'].update(reason='one fork fewer on the release', slice='M2 scopes')
    lines['pC'].update(reason='the driver is not installed', slice='driver')
    lines['pD'].update(reason='U-01', slice='M5 the failure walk')
    green = L.render(BUILDS, order, lines)
    written = {name: next(text for text in green.split('\n') if text.startswith(name + '\t')) for name in order}
    column = {title: index for index, title in enumerate(L.columns(BUILDS))}

    def with_entry(name, title, value):
        changed = written[name].split('\t')
        changed[column[title]] = value
        return green.replace(written[name], '\t'.join(changed))

    control('green: the ledger of the observations holds', judged(green)[0] == [], judged(green)[0])
    control('green: promote keeps the hand columns and is a fixed point',
            L.render(BUILDS, *carry(BUILDS, L.parse(green, BUILDS)[1], names, observed)) == green)
    control('green: a ledger that was read whole may be promoted over, and so may no ledger',
            unpromotable(green, L.parse(green, BUILDS)[1]) is None and unpromotable(None, {}) is None)
    short = green.replace(written['pD'], '\t'.join(written['pD'].split('\t')[:5]))
    red('a promote over a ledger with a line that was not read',
        [unpromotable(short, judged(short)[2]) or ''], 'has 4 line(s) and 3 could be read')
    red('a promote over a ledger for other builds',
        [unpromotable(green.replace(f'{release} exit', '4.0.2 exit'),
                      judged(green.replace(f'{release} exit', '4.0.2 exit'))[2]) or ''],
        'has 4 line(s) and 0 could be read')
    control('the expected differences of a ledger are listed by program and build, with slice and reason',
            L.known(BUILDS, order, lines) == [
                f'pB: {release} schedule: no: the host lacks machine rows 1-3 (forked 0 1, started 1, exited 1 success) '
                '(M2 scopes: one fork fewer on the release)',
                f'pC: {release} exit, schedule, sync: not-run (driver: the driver is not installed)',
                f'pD: {pin} exit: no: machine interrupt [{{"interrupt":0}}], host fail [{{"fail":42}}] '
                '(M5 the failure walk: U-01)',
                f'pD: {pin} schedule: no: machine row 1 (exited 0 interrupt) is host row 1 (exited 0 fail) '
                '(M5 the failure walk: U-01)'], L.known(BUILDS, order, lines))

    # an entry that leaves its line, in the ledger or in the host run
    red('a `yes` entry changed to `no` in the ledger', judged(with_entry('pA', f'{pin} exit', 'no: x'))[0],
        f'pA: {pin} exit: the ledger says "no: x", observed "yes"')
    red('a `no` entry changed to `yes` in the ledger', judged(with_entry('pB', f'{release} schedule', 'yes'))[0],
        f'pB: {release} schedule: the ledger says "yes", observed "no: the host lacks machine rows 1-3')
    red('a `no` whose difference changed shape',
        judged(green.replace('machine rows 1-3', 'machine rows 1-2'))[0],
        f'pB: {release} schedule: the ledger says "no: the host lacks machine rows 1-2')
    red('a program that leaves its line in the host run',
        judged(green, [report('pA', runSyncAgree=False, hostSync={'exit': {'success': 2}}), b_release,
                       report('pD')])[0],
        f'pA: {release} sync: the ledger says "yes", observed "no: machine success 1, host success 2"')

    # the coordinator's first control: a known difference in one field excuses no other field
    red('a known schedule difference, and the exit moves in the host run',
        judged(green, [report('pA'), dict(b_release, exitAgree=False, hostExit='success 2'), report('pD')])[0],
        f'pB: {release} exit: the ledger says "yes", observed "no: machine success 1, host success 2"',
        absent=[f'pB: {release} schedule', f'pB: {release} sync'])
    red('a known schedule difference, and the sync exit moves in the host run',
        judged(green, [report('pA'), dict(b_release, runSyncAgree=False, hostSync={'exit': {'success': 2}}),
                       report('pD')])[0],
        f'pB: {release} sync: the ledger says "yes", observed "no: machine success 1, host success 2"',
        absent=[f'pB: {release} schedule', f'pB: {release} exit'])
    red('a known schedule difference, and the expected exit is altered in the ledger',
        judged(with_entry('pB', f'{release} exit', 'no: machine success 1, host success 2'))[0],
        f'pB: {release} exit: the ledger says "no: machine success 1, host success 2", observed "yes"',
        absent=[f'pB: {release} schedule'])

    # the coordinator's second control: a missing observation is neither agreement nor disagreement
    red('a required observation removed from the release result',
        [raises(lambda: judged(green, [report('pA'), report('pD')]), L.Inconsistent)],
        'pB: the runner reports no result for it')
    red('a required observation removed from the committed pin result',
        [raises(lambda: judged(green, None, [report('pA'), report('pB'), d_pin]), L.Inconsistent)],
        'pC: the runner reports no result for it')
    red('a field of a program that ran is null',
        judged(green, [report('pA', runSyncAgree=None), b_release, report('pD')])[0],
        f'pA: {release} sync: the ledger says "yes", observed "n/a"')
    without_exit = report('pA')
    del without_exit['exitAgree']
    red('a field of a program that ran is absent',
        judged(green, [without_exit, b_release, report('pD')])[0],
        f'pA: {release} exit: the ledger says "yes", observed "n/a"')
    red('a program that was not run where the ledger says `yes`',
        judged(with_entry('pC', f'{release} exit', 'yes'))[0],
        f'pC: {release} exit: the ledger says "yes", observed "not-run"')
    red('a program that ran where the ledger says `not-run`',
        judged(green, [report('pA'), b_release, report('pC'), report('pD')], skip={})[0],
        f'pC: {release} exit: the ledger says "not-run", observed "yes"')
    red('a `not-run` line without its reason',
        judged(green.replace('\tthe driver is not installed\t', '\t\t'))[0],
        'pC: an entry is not `yes`, so the line needs a reason and a slice')
    red('a program the lane did not select and the runner reports',
        [raises(lambda: judged(green, [report('pA'), b_release, report('pC'), report('pD')]), L.Inconsistent)],
        'pC: the lane did not select it, and the runner reports it')
    red('a program the manifest does not name',
        [raises(lambda: judged(green, on_release + [dict(report('pA'), program='pZ')]), L.Inconsistent)],
        'pZ, which the manifest does not name')

    # the file's own rules
    red('a line missing', judged(green.replace(written['pA'] + '\n', ''))[0],
        'pA: the manifest has this program and the ledger has no line for it')
    red('a line for no program', judged(green + written['pA'].replace('pA', 'pZ') + '\n')[0],
        'pZ: the ledger has a line for it and the manifest has no such program')
    red('lines out of the manifest\'s order',
        judged(green.replace(written['pA'] + '\n' + written['pB'], written['pB'] + '\n' + written['pA']))[0],
        'the lines are not in the manifest\'s order: program 1 is pB, the manifest has pA there')
    red('a second line for one program', judged(green + written['pA'] + '\n')[0],
        'pA: a second line for this program')
    red('a difference without its reason', judged(green.replace('\tU-01\t', '\t\t'))[0],
        'pD: an entry is not `yes`, so the line needs a reason and a slice')
    red('a difference without its slice', judged(green.replace('\tM5 the failure walk', '\t'))[0],
        'pD: an entry is not `yes`, so the line needs a reason and a slice')
    red('a slice the plan does not name', judged(green.replace('M2 scopes', 'M9 scopes'))[0],
        'pB: the slice "M9 scopes" must open with one of')
    red('a reason left on an agreeing line', judged(with_entry('pA', 'reason', 'stale'))[0],
        'pA: every entry is `yes`, so reason and slice must be empty')
    red('an entry that is none of the four', judged(with_entry('pA', f'{pin} exit', 'maybe'))[0],
        f'pA: {pin} exit: "maybe" is not')
    red('a `no` without its difference', judged(with_entry('pA', f'{pin} exit', 'no:'))[0],
        f'pA: {pin} exit: "no:" is not')
    red('a line with an entry too few',
        judged(green.replace(written['pA'], '\t'.join(written['pA'].split('\t')[:6])))[0],
        '6 columns, the header has 9', 'pA: the manifest has this program and the ledger has no line for it')
    red('a line with a column too many', judged(green.replace(written['pA'], written['pA'] + '\textra'))[0],
        '10 columns, the header has 9')
    trimmed = '\n'.join(text.rstrip('\t') for text in green.split('\n'))
    control('green: a ledger whose trailing empty columns were trimmed says the same',
            trimmed != green and judged(trimmed)[0] == [] and L.parse(trimmed, BUILDS)[:2] == L.parse(green, BUILDS)[:2],
            judged(trimmed)[0])
    red('a trimmed line that still needs its slice',
        judged(green.replace('\tM5 the failure walk', ''))[0],
        'pD: an entry is not `yes`, so the line needs a reason and a slice')
    red('a header for other builds', judged(green.replace(f'{release} exit', '4.0.2 exit'))[0],
        f'the ledger is not read: line {L.HEAD.count(chr(10)) + 1}: the header must be program | {pin} exit')
    red('an empty file', judged('')[0], 'the ledger is not read: the ledger has no header')
    red('no file', judged(None)[0], 'the ledger is missing')

    # the record of a host run
    kept = {'manifest': {'sha256': 'aa', 'programs': 4},
            'builds': {release: {'runtime': {'bun': '1.4.2'}, 'modules': {'count': 3, 'sha256': 'bb'},
                                 'programs': {'notRun': ['pC']}}}}
    same = json.dumps(kept)
    control('green: the record of this host run is accepted', record_findings(kept, same) == [])
    red('the record of other modules',
        record_findings(kept, same.replace('"bb"', '"cc"')),
        f'build-ledger.run.json: builds.{release}.modules.sha256: recorded "cc", this run "bb"')
    red('the record of another runtime', record_findings(kept, same.replace('1.4.2', '1.4.3')),
        f'builds.{release}.runtime.bun: recorded "1.4.3", this run "1.4.2"')
    red('the record of a host run that ran every program', record_findings(kept, same.replace('["pC"]', '[]')),
        f'builds.{release}.programs.notRun: recorded [], this run ["pC"]')
    red('a record with a field this host run does not have',
        record_findings(kept, same.replace('"programs": 4', '"programs": 4, "extra": 1')),
        'manifest.extra: recorded only')
    red('no record', record_findings(kept, None), 'build-ledger.run.json is missing')
    red('a record that is no JSON', record_findings(kept, '{'), 'build-ledger.run.json is not JSON')
    control('the digest of a set names its files and does not depend on their order',
            digest({'a': b'1', 'b': b'2'}) == digest({'b': b'2', 'a': b'1'})
            and len({digest({'a': b'1', 'b': b'2'}), digest({'a': b'12', 'b': b''}), digest({'a': b'1'}),
                     digest({'a': b'1', 'c': b'2'})}) == 4)

    # the identity of what a build ran: its modules and its tapes against the committed ones
    ran = [by_name['pA'], by_name['pB']]
    kept_modules = {'pA.ts': b'a', 'pB.ts': b'b', 'pC.ts': b'c'}
    kept_tapes = {'pB.jsonl': b't'}
    same = lambda modules, tapes: same_as_committed(ran, release, modules, kept_modules, tapes, kept_tapes)  # noqa: E731
    control('green: the committed modules of the programs that ran, and their committed tapes',
            same({'pA.ts': b'a', 'pB.ts': b'b'}, {'pB.jsonl': b't'}) == ([], []))
    red('a module that is not the committed module', same({'pA.ts': b'a', 'pB.ts': b'B'}, {'pB.jsonl': b't'})[0],
        'generated/pB.ts')
    red('a module of a program that did not run', same({'pA.ts': b'a', 'pB.ts': b'b', 'pC.ts': b'c'},
                                                       {'pB.jsonl': b't'})[0], 'generated/pC.ts')
    red('a program that ran without its module', same({'pA.ts': b'a'}, {'pB.jsonl': b't'})[0], 'generated/pB.ts')
    red('a tape that is not the committed tape', same({'pA.ts': b'a', 'pB.ts': b'b'}, {'pB.jsonl': b'T'})[1],
        f'pB: {release} tape: the build answered a host row differently from harness/truth/tapes/pB.jsonl')
    red('a committed tape that the build did not record', same({'pA.ts': b'a', 'pB.ts': b'b'}, {})[1],
        f'pB: {release} tape: not recorded on this build, committed for the pin')
    red('a tape that the pin does not have', same({'pA.ts': b'a', 'pB.ts': b'b'},
                                                  {'pA.jsonl': b'x', 'pB.jsonl': b't'})[1],
        f'pA: {release} tape: recorded on this build, not committed for the pin')
    red('a tape of a program that did not run', same({'pA.ts': b'a', 'pB.ts': b'b'},
                                                     {'pB.jsonl': b't', 'pC.jsonl': b'x'})[1],
        f'pC.jsonl: {release} tape: recorded for a program the lane did not run')

    # the host tests' count
    counted = 'bun test v1.4.2\n\n 23 pass\n 0 fail\n 175 expect() calls\nRan 23 tests across 4 files. [1.00ms]\n'
    control('green: a `bun test` run that passes gives its count', tests_passed(0, counted) == '23')
    control('red: a `bun test` run with a failed test, a nonzero status, no test or no count is refused',
            [tests_passed(0, counted.replace(' 0 fail', ' 1 fail')), tests_passed(1, counted),
             tests_passed(0, counted.replace(' 23 pass', ' 0 pass')), tests_passed(0, 'bun test v1.4.2\n')] == [None] * 4)

    # the import rewrite and the closure
    source = ('import { Effect } from "effect"\nimport { KeyValueStore } from "effect/unstable/persistence"\n'
              'import * as Reactivity from \'effect/unstable/reactivity/Reactivity\'\n'
              'import {\n  SqliteClient,\n  type Other\n} from "@effect/sql-sqlite-bun"\n'
              'export * from "./a.gen.ts"\nimport "./side.ts"\n'
              '/** import { X } from "effect/unstable/sql" stays: a comment */\n'
              'export const text = "effect/unstable/persistence"\n'
              'const later = await import("effect/unstable/sql")\n')
    table = dict(truth_host.RELEASE_ENTRY_POINTS, **{truth_host.DRIVER: './' + STUB})
    text, done = rewrite(source, table)
    control('the rewrite moves each import of the table and nothing else',
            done == [('effect/unstable/persistence', 'effect/persistence'),
                     ('effect/unstable/reactivity/Reactivity', 'effect/reactivity/Reactivity'),
                     (truth_host.DRIVER, './' + STUB)]
            and text == source.replace('from "effect/unstable/persistence"', 'from "effect/persistence"')
            .replace("'effect/unstable/reactivity/Reactivity'", "'effect/reactivity/Reactivity'")
            .replace('from "@effect/sql-sqlite-bun"', f'from "./{STUB}"'), done)
    control('the specifiers of a source are its static imports and re-exports',
            specifiers(source) == ['effect', 'effect/unstable/persistence', 'effect/unstable/reactivity/Reactivity',
                                   truth_host.DRIVER, './a.gen.ts', './side.ts'], specifiers(source))
    tree = {'h/t/run.ts': 'import "./p.ts"\nimport { a } from "../../ts/e/q.ts"\nimport { E } from "effect"\n',
            'h/t/p.ts': 'export * from "./s/k.ts"\n', 'h/t/s/k.ts': 'import "../p.ts"\n', 'ts/e/q.ts': '',
            'h/t/control.ts': 'import "./p.ts"\n', 'h/t/unreached.ts': ''}
    control('the closure is what the entries reach, the entries first',
            closure(tree.get, ['h/t/run.ts', 'h/t/control.ts']) ==
            ['h/t/run.ts', 'h/t/control.ts', 'h/t/p.ts', 'ts/e/q.ts', 'h/t/s/k.ts'],
            closure(tree.get, ['h/t/run.ts', 'h/t/control.ts']))
    control('red: an import of no file is refused',
            'h/t/run.ts imports ./gone.ts' in raises(
                lambda: closure(dict(tree, **{'h/t/run.ts': 'import "./gone.ts"\n'}).get, ['h/t/run.ts']), LaneError))
    control('red: an import that leaves the repository is refused',
            'which is no file of the repository' in raises(
                lambda: closure(dict(tree, **{'h/t/run.ts': 'import "../../../out.ts"\n'}).get, ['h/t/run.ts']),
                LaneError))

    # the exports of a package, and a specifier the table does not place
    exports = {'.': './dist/index.js', './persistence': './dist/persistence/index.js', './*': './dist/*.js',
               './internal/*': None, './*/index': None, './index': None}
    files = {'./dist/index.js', './dist/persistence/index.js', './dist/reactivity/Reactivity.js'}
    control('an exact export, a pattern, and the patterns that close a path',
            [export_target(exports, s) for s in ('.', './persistence', './reactivity/Reactivity',
                                                 './internal/core', './sql/index', './index')] ==
            ['./dist/index.js', './dist/persistence/index.js', './dist/reactivity/Reactivity.js', None, None, None])
    accept = lambda spec, driver=False: unresolved(spec, exports, files.__contains__, driver)  # noqa: E731
    control('the accepted specifiers: effect, an exported path, a builtin, a present driver',
            [accept('effect'), accept('effect/persistence'), accept('effect/reactivity/Reactivity'),
             accept('node:fs'), accept(truth_host.DRIVER, True)] == [None] * 5)
    control('red: an entry point the table does not map is refused',
            'no file' in (accept('effect/unstable/persistence') or ''), accept('effect/unstable/persistence'))
    control('red: a closed path of effect is refused', 'does not export it' in (accept('effect/internal/core') or ''))
    control('red: the driver is refused when the install has none',
            'not a driver of the selected install' in (accept(truth_host.DRIVER) or ''))
    control('red: any other package is refused', 'not a path of effect' in (accept('fast-check', True) or ''))

    # the driver test
    control('a module that mentions `Sql.` needs the driver, and no other does',
            [needs_driver(item) for item in manifest['programs']] == [False, False, True, False]
            and not needs_driver(program('pE', plain, 'export const main = Effect.fail(pair("SqlError", "boom"))\n'))
            and needs_driver({'decl': None, 'expr': 'Sql.close(a0)'}))

    # the selection and the entry-point table, on scratch installs
    with tempfile.TemporaryDirectory() as scratch:
        def install(name, effect, driver=None, compiler=None):
            modules = Path(scratch) / name / 'node_modules'
            for package, version in (('effect', effect), (truth_host.DRIVER, driver),
                                     ('@typescript/native-preview', compiler)):
                if version is not None:
                    (modules / package / 'bin').mkdir(parents=True)
                    (modules / package / 'package.json').write_text(json.dumps({'version': version}))
                    (modules / package / 'bin/tsgo').write_text('')
            modules.mkdir(parents=True, exist_ok=True)
            return {truth_host.RELEASE_ENV: str(modules)}

        def selection(environ):
            return raises(lambda: truth_host.release_install(environ), SystemExit)

        control('red: no selection, no default', f'set {truth_host.RELEASE_ENV}' in selection({}))
        control('red: an install without effect', 'found no effect package' in selection(install('empty', None)))
        control('red: the pin where the release is asked',
                f'must contain effect@{release} (found effect@{pin}' in selection(install('pin', pin, pin)))
        control('red: the release with the pin\'s driver',
                f'holds {truth_host.DRIVER}@{pin}' in selection(install('mixed', release, pin)))
        bare = truth_host.release_install(install('bare', release))
        control('green: the release without the driver is accepted', bare[1] is False and bare[0].name == 'node_modules')
        control('green: the release with its driver is accepted',
                truth_host.release_install(install('whole', release, release))[1] is True)
        refusal = lambda environ: truth_host.compiler_refusal(Path(environ[truth_host.RELEASE_ENV]), '7.0.0')  # noqa: E731
        control('red: an install without the compiler',
                'must contain @typescript/native-preview@7.0.0' in (refusal(install('no-compiler', release)) or ''))
        control('red: an install with another compiler',
                'holds @typescript/native-preview@6.9.9' in (refusal(install('old', release, None, '6.9.9')) or ''))
        control('green: an install with the pinned compiler', refusal(install('good', release, None, '7.0.0')) is None)

        def package(name, exports, files):
            modules = Path(scratch) / name / 'node_modules'
            (modules / 'effect').mkdir(parents=True)
            (modules / 'effect/package.json').write_text(json.dumps({'exports': exports}))
            for file in files:
                (modules / 'effect' / file).parent.mkdir(parents=True, exist_ok=True)
                (modules / 'effect' / file).write_text('')
            return modules

        old_shape = package('shape-pin', {
            '.': './dist/index.js', './*': './dist/*.js', './unstable/persistence': './dist/unstable/persistence/index.js',
            './unstable/sql': './dist/unstable/sql/index.js'},
            ['dist/index.js', 'dist/unstable/persistence/index.js', 'dist/unstable/sql/index.js',
             'dist/unstable/reactivity/Reactivity.js'])
        new_shape = package('shape-release', {
            '.': './dist/index.js', './*': './dist/*.js', './persistence': './dist/persistence/index.js',
            './sql': './dist/sql/index.js'},
            ['dist/index.js', 'dist/persistence/index.js', 'dist/sql/index.js', 'dist/reactivity/Reactivity.js'])
        control('green: the table is true of a pin-shaped and a release-shaped package',
                entry_point_findings({pin: (old_shape, True), release: (new_shape, False)}) == [],
                entry_point_findings({pin: (old_shape, True), release: (new_shape, False)}))
        red('the table against two packages of the pin\'s shape',
            entry_point_findings({pin: (old_shape, True), release: (old_shape, False)}),
            f'effect@{release} exports "effect/unstable/persistence"',
            f'effect@{release} does not export "effect/sql"')

    print(f'self-test: {sum(outcomes)} of {len(outcomes)} controls as expected')
    return 0 if all(outcomes) else 1


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    tests = []
    if '--host-tests' in argv:
        at = argv.index('--host-tests')
        argv, tests = argv[:at], argv[at + 1:]
        if not tests or any(test.startswith('-') for test in tests):
            print(__doc__)
            return 2
    if argv not in ([], ['--promote']):
        print(__doc__)
        return 2
    try:
        return lane(promote=bool(argv), tests=tests)
    except (LaneError, truth_ledger.Inconsistent) as refusal:
        print(f'FAIL truth-release: {refusal}')
        return 1
    except subprocess.TimeoutExpired as late:
        print(f'FAIL truth-release: {Path(late.cmd[0]).name} did not finish in {late.timeout:.0f} s: '
              f'{" ".join(str(part) for part in late.cmd[1:4])} ...')
        return 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
