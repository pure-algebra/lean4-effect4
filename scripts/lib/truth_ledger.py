"""The build ledger of the truth lanes: each program's expected agreement with each build.

`harness/truth/build-ledger.tsv` has one line per program of the truth manifest
(`harness/truth/corpus.json`), in the manifest's order. A line gives, for each build and each
compared field, what the comparison of the Lean machine with that build's host run must say:

    program | <pin> exit | <pin> schedule | <pin> sync | <release> exit | ... | reason | slice

The compared fields are the runner's three (`harness/truth/run-truth.ts`): `exit`, the verdict
entry's exit; `schedule`, the fork entry's schedule without its `scheduled` rows; `sync`, the
exit of `runSyncExit`. An entry of the ledger is one of

    yes               the two faces agree on the field
    no: <difference>  they disagree, and this is the difference: both exits, or the edit that
                      turns the machine's schedule into the host's
    not-run           the lane did not run the program on this build
    n/a               the runner gives no verdict on the field (no module to run, or the field
                      is absent from its result)

A `no` carries its difference, so a disagreement that changes shape leaves its line as an
agreement that breaks does. Each entry is judged alone: a known difference in one field
excuses no other field. A missing observation is neither agreement nor disagreement: it is
`not-run` or `n/a`, and never `yes`. `reason` and `slice` are written by hand: both are empty
exactly when all six entries are `yes`, and otherwise `reason` says why in a few words and
`slice` names the owner, a slice of the migration plan (`M0` to `M8`) or `driver`.

This module is the pure part: the file's grammar (`parse`, `render`), the observation of a
runner result (`observe`, `entries_of`) and the comparison (`judge`). It reads no file and starts
no process; `scripts/check-truth-release.py` does both and holds the controls (`--self-test`).
The header names the builds, so a ledger written for other builds is refused, not reread.
"""
import difflib
import json
import re

FIELDS = ('exit', 'schedule', 'sync')
HAND = ('reason', 'slice')
YES, NOT_RUN, NA, NO = 'yes', 'not-run', 'n/a', 'no: '
SLICES = ('M0', 'M1', 'M2', 'M3', 'M4', 'M5', 'M6', 'M7', 'M8', 'driver')

HEAD = '''\
# The build ledger of the truth lanes (harness/truth/RELEASE-LANE.md; decisions row 248).
# One line per program of harness/truth/corpus.json, in its order. An entry is the expected
# comparison of the Lean machine with one build on one field: `yes`, `no: <the difference>`,
# `not-run` or `n/a`. `reason` and `slice` are empty exactly when all six entries are `yes`.
# The entries are measured: `make gen-truth-ledger` writes them and keeps `reason` and `slice`,
# which are written by hand. `make check-truth-release` judges the file.
# What the entries were measured on is build-ledger.run.json, which the same command writes.
'''


def columns(builds):
    return ['program'] + [f'{build} {field}' for build in builds for field in FIELDS] + list(HAND)


def one_line(text):
    """A text for one column: every run of white space is one space."""
    return re.sub(r'\s+', ' ', str(text)).strip()


def all_yes(line, builds):
    return all(line['entries'][(build, field)] == YES for build in builds for field in FIELDS)


def agrees(line, build):
    return all(line['entries'][(build, field)] == YES for field in FIELDS)


# ---- the file ------------------------------------------------------------------------------

class Unreadable(Exception):
    """A text that is no ledger of these builds: it has no header, or another header."""


def parse(text, builds):
    """`(order, lines, findings)` of a ledger text; raises `Unreadable` without its header.

    `order` is the programs in file order. `lines` maps a program to its `entries` (by
    `(build, field)`), its `reason` and its `slice`. `findings` lists every defect of a line,
    each with its line number in the file. A line with a defect is still judged where it was
    read, so one changed entry gives both its defect and the finding that names both values.
    """
    want = columns(builds)
    order, lines, findings = [], {}, []
    body = [(number, text_line) for number, text_line in enumerate(text.split('\n'), 1)
            if text_line and not text_line.startswith('#')]
    if not body:
        raise Unreadable('the ledger has no header')
    number, text_line = body[0]
    if text_line.split('\t') != want:
        raise Unreadable(f'line {number}: the header must be {" | ".join(want)} '
                         f'(the builds are {" and ".join(builds)})')
    for number, text_line in body[1:]:
        values = text_line.split('\t')
        if len(values) != len(want):
            findings.append(f'line {number}: {len(values)} columns, the header has {len(want)}')
            continue
        name = values[0]
        if any(value != one_line(value) for value in values):
            findings.append(f'line {number}: {name}: a column has leading, trailing or doubled white space')
        if not name:
            findings.append(f'line {number}: the program column is empty')
            continue
        if name in lines:
            findings.append(f'line {number}: {name}: a second line for this program')
            continue
        line = {'entries': {}, 'reason': values[-2], 'slice': values[-1]}
        for (build, field), value in zip([(b, f) for b in builds for f in FIELDS], values[1:-2]):
            line['entries'][(build, field)] = value
            if value not in (YES, NOT_RUN, NA) and not (value.startswith(NO) and len(value) > len(NO)):
                findings.append(f'line {number}: {name}: {build} {field}: "{value}" is not '
                                f'`{YES}`, `{NOT_RUN}`, `{NA}` or `{NO}<the difference>`')
        order.append(name)
        lines[name] = line
        if all_yes(line, builds):
            if line['reason'] or line['slice']:
                findings.append(f'line {number}: {name}: every entry is `{YES}`, so reason and slice must be empty')
        else:
            if not line['reason'] or not line['slice']:
                findings.append(f'line {number}: {name}: an entry is not `{YES}`, so the line needs a reason '
                                f'and a slice')
            elif line['slice'].split(' ')[0] not in SLICES:
                findings.append(f'line {number}: {name}: the slice "{line["slice"]}" must open with one of '
                                + ', '.join(SLICES))
    return order, lines, findings


def render(builds, order, lines):
    out = ['\t'.join(columns(builds))]
    for name in order:
        line = lines[name]
        out.append('\t'.join([name] + [line['entries'][(b, f)] for b in builds for f in FIELDS]
                             + [line['reason'], line['slice']]))
    return HEAD + '\n'.join(out) + '\n'


# ---- the observation -----------------------------------------------------------------------

def compared(schedule):
    """A schedule as the runner compares it: without its `scheduled` rows."""
    return [row for row in schedule if not row.startswith('scheduled ')]


def _rows(lo, hi):
    return f'row {lo}' if hi - lo == 1 else f'rows {lo}-{hi - 1}'


def schedule_difference(machine, host):
    """The edit that turns the machine's compared schedule into the host's, in words.

    Exact: the machine's rows and this text give the host's rows. Rows count from 0, as the
    runner's own note counts them. Empty when the two schedules are equal.
    """
    parts = []
    matcher = difflib.SequenceMatcher(None, machine, host, autojunk=False)
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == 'delete':
            parts.append(f'the host lacks machine {_rows(i1, i2)} ({", ".join(machine[i1:i2])})')
        elif tag == 'insert':
            parts.append(f'the host adds before machine row {i1} ({", ".join(host[j1:j2])})')
        elif tag == 'replace':
            parts.append(f'machine {_rows(i1, i2)} ({", ".join(machine[i1:i2])}) '
                         f'is host {_rows(j1, j2)} ({", ".join(host[j1:j2])})')
    return '; '.join(parts)


def exit_kind(exit):
    """The kind of a wired exit, with the runner's precedence (`exitKindOf`): fail, interrupt, die."""
    if not isinstance(exit, dict):
        return '?'
    if 'success' in exit:
        return 'success'
    reasons = (exit.get('failure') or {}).get('reasons') or []
    for kind in ('fail', 'interrupt', 'die'):
        if any(kind in reason for reason in reasons):
            return kind
    return 'empty'


def render_exit(exit):
    """A wired exit as the runner prints one (`renderExit`)."""
    if exit is None:
        return 'no exit'
    compact = lambda value: json.dumps(value, separators=(',', ':'), ensure_ascii=False)  # noqa: E731
    kind = exit_kind(exit)
    if kind == 'success':
        return f'success {compact(exit["success"])}'
    return f'{kind} {compact((exit.get("failure") or {}).get("reasons") or [])}'


class Inconsistent(Exception):
    """A runner result that cannot be observed: it contradicts its own schedules, or it does
    not report exactly the programs the lane selected."""


def entries_of(program, report):
    """One program's three entries on one build: `program` is its manifest item, `report` the
    runner's result for it, or `None` when the lane did not run it.

    A missing observation is neither agreement nor disagreement: a program that was not run is
    `not-run`, and a field the report does not give (absent or null) is `n/a`. Only the
    runner's `true` is `yes`.
    """
    if report is None:
        return dict.fromkeys(FIELDS, NOT_RUN)
    name, out = program['name'], {}
    host_exit = str(report.get('hostExit', ''))

    agree = report.get('exitAgree')
    if agree is None:
        out['exit'] = NA
    elif agree is True:
        out['exit'] = YES
    elif host_exit.startswith('module failed to load'):
        # the message holds a path of the work copy, which is no part of the observation
        out['exit'] = NO + 'the module failed to load'
    elif host_exit.startswith('main is not an Effect'):
        out['exit'] = NO + 'main is not an Effect'
    else:
        out['exit'] = NO + one_line(f'machine {report.get("leanExit")}, host {host_exit}')

    agree = report.get('scheduleAgree')
    if agree is None:
        out['schedule'] = NA
    else:
        # The runner's verdict, checked against the schedules it compared: this module's
        # difference is empty exactly when the runner says the schedules agree.
        host = (report.get('host') or {}).get('schedule')
        if host is None:
            raise Inconsistent(f'{name}: the runner gives a schedule verdict and no host schedule')
        difference = schedule_difference(compared(program['run']['schedule']), compared(host))
        if (agree is True) != (difference == ''):
            raise Inconsistent(f'{name}: the runner says the schedules {"agree" if agree else "differ"}, and '
                               f'the compared schedules {"differ: " + difference if difference else "are equal"}')
        out['schedule'] = YES if agree is True else NO + difference

    agree = report.get('runSyncAgree')
    if agree is None:
        out['sync'] = NA
    elif agree is True:
        out['sync'] = YES
    else:
        host_sync = report.get('hostSync') or {}
        out['sync'] = NO + one_line(f'machine {render_exit(program["runSync"]["exit"])}, '
                                    f'host {render_exit(host_sync.get("exit"))}')
    return out


def observe(manifest, result, not_run=()):
    """`{program: entries}` for one build: every program of the manifest, from the runner's
    result. A program in `not_run` must be absent from the result; any other program must be
    in it. Raises `Inconsistent` otherwise: a program is never silently unobserved."""
    by_name = {report['program']: report for report in result['rows']}
    names = [program['name'] for program in manifest['programs']]
    stray = sorted(set(by_name) - set(names))
    if stray:
        raise Inconsistent(f'the runner reports {", ".join(stray)}, which the manifest does not name')
    observed = {}
    for program in manifest['programs']:
        name = program['name']
        if name in not_run:
            if name in by_name:
                raise Inconsistent(f'{name}: the lane did not select it, and the runner reports it')
            observed[name] = entries_of(program, None)
        elif name not in by_name:
            raise Inconsistent(f'{name}: the runner reports no result for it')
        else:
            observed[name] = entries_of(program, by_name[name])
    return observed


# ---- the comparison ------------------------------------------------------------------------

def judge(builds, order, lines, programs, observed):
    """The findings of a ledger against the observations: `observed[build][program][field]`.

    A program that leaves its line gives one finding that names the program, the build, the
    field and both values. Each of the six entries is compared alone. `observed` may hold one
    build only; the other build's entries are then not judged. Empty when the ledger holds.
    """
    findings = []
    missing = [name for name in programs if name not in lines]
    unknown = [name for name in order if name not in programs]
    for name in missing:
        findings.append(f'{name}: the manifest has this program and the ledger has no line for it')
    for name in unknown:
        findings.append(f'{name}: the ledger has a line for it and the manifest has no such program')
    if not missing and not unknown and order != list(programs):
        first = next(i for i, (a, b) in enumerate(zip(order, programs)) if a != b)
        findings.append(f'the lines are not in the manifest\'s order: program {first + 1} is {order[first]}, '
                        f'the manifest has {programs[first]} there')
    for build in builds:
        if build not in observed:
            continue
        for name in programs:
            if name not in lines:
                continue
            for field in FIELDS:
                expected, seen = lines[name]['entries'][(build, field)], observed[build][name][field]
                if expected != seen:
                    findings.append(f'{name}: {build} {field}: the ledger says "{expected}", observed "{seen}"')
    return findings


def classes(builds, order, lines):
    """How many programs agree with both builds, with one only, or with neither, and how many
    the release lane did not run: the counts of the summary."""
    pin, release = builds
    count = {'both': 0, 'pin only': 0, 'release only': 0, 'neither': 0, 'not run': 0}
    for name in order:
        line = lines[name]
        a, b = agrees(line, pin), agrees(line, release)
        count['both' if a and b else 'pin only' if a else 'release only' if b else 'neither'] += 1
        count['not run'] += any(line['entries'][(release, field)] == NOT_RUN for field in FIELDS)
    return count
