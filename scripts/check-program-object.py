#!/usr/bin/env python3
"""Exercise object saving, application-free opening, and direct compiler readings.

Build `effect4` and `Effect4.Tool.Serve` first. Run this script from any directory.
The controls use temporary files and invoke no host or target runtime.
"""
import json
import os
import shlex
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/effect4'
FIXTURE = r'''
import Compiler.Groups
import Effect4.Tool.Serve

open Effect4 Effect4.Program Effect4.Store Compiler

def main (args : List String) : IO UInt32 := do
  let b ← match Compiler.check Test.Dogfood.Scenario.Todo.application with
    | .ok b => pure b
    | .error why => IO.eprintln why.text; return 1
  match args with
  | ["fixtures", folder] =>
    IO.FS.writeBinFile (folder ++ "/bare.node") ⟨(nodeOf b.program).encode.toArray⟩
    let bad : Object := ⟨{}, b.program⟩
    IO.FS.writeBinFile (folder ++ "/ill-typed.obj") ⟨bad.bytes.toArray⟩
    match bad.open with
    | .ok _ => return 1
    | .error why =>
      IO.FS.writeFile (folder ++ "/admission.json") (jsonText (tree why))
    return 0
  | ["refuse", file] =>
    let arguments := ["check", "--out", file]
    Compiler.run (.programs "bad" [("bad", b.program)]) {} arguments arguments
  | ["readings"] =>
    let state := (Tool.serve Check.Oracle.uncached Tool.empty
      (.act (.open_ "todo" b.app ⟨b.program, []⟩))).value.1
    let table := (Tool.serve Check.Oracle.uncached state (.ask .table)).value.2.result
    let doc := (Tool.serve Check.Oracle.uncached state (.ask (.doc (some [])))).value.2.result
    let .ok (.table entries) := table | return 1
    let .ok (.doc { inspection := some inspection, .. }) := doc | return 1
    for (name, reading) in [("types", typesReading entries),
        ("rows", rowsReading inspection.context.allRows),
        ("graph", graphReading inspection.expected), ("surface", surfaceReading b.program)] do
      IO.println (jsonText (.obj [("name", .str name), ("text", .str reading.text),
        ("json", .str (jsonText reading.json))]))
    return 0
  | _ => return 2
'''


def run(command, expected=0, cwd=ROOT):
    env = dict(os.environ, LEAN_NUM_THREADS='3')
    result = subprocess.run([str(x) for x in command], cwd=cwd, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if result.returncode != expected:
        raise AssertionError(f'{command}: expected {expected}, got {result.returncode}\n'
                             f'{result.stdout}{result.stderr}')
    return result


def main():
    if not BINARY.is_file():
        raise SystemExit('Build first: LEAN_NUM_THREADS=3 lake build effect4 Effect4.Tool.Serve')
    checks = 0

    def passed(label):
        nonlocal checks
        checks += 1
        print(f'PASS {label}')

    with tempfile.TemporaryDirectory(prefix='effect4-object-') as directory:
        folder = Path(directory)
        obj = folder / 'todo.obj'
        first = run([BINARY, 'check', '--group', 'todo', '--json'])
        saved = run([BINARY, 'check', '--group', 'todo', '--json', '--out', obj])
        assert saved.stdout == first.stdout and not saved.stderr
        content = obj.read_bytes()
        run([BINARY, 'check', '--group', 'todo', '--out', obj, '--json'])
        assert obj.read_bytes() == content
        passed('saving preserves certificate JSON and repeats identical bytes')

        plain = run([BINARY, 'check', '--group', 'todo'])
        plain_saved = run([BINARY, 'check', '--group', 'todo', '--out', obj])
        assert plain.stdout == plain_saved.stdout
        passed('saving preserves text check output')

        opened = run([BINARY, 'open', obj], cwd=folder)
        assert opened.stdout == first.stdout and not opened.stderr
        passed('open outside the project needs no group, source, or prelude')

        for args in [['open'], ['open', obj, 'extra'], ['open', '--json'],
                     ['open', obj, '--group', 'todo'],
                     ['check', '--group', 'todo', '--out'],
                     ['check', '--group', 'todo', '--out', '--json'],
                     ['check', '--group', 'todo', '--bogus'],
                     ['check', '--group', 'todo', '--out', obj, '--out', obj],
                     ['check', '--group', 'corpus', '--out', obj]]:
            result = run([BINARY, *args], 2)
            assert not result.stdout and 'usage:' in result.stderr
            assert obj.read_bytes() == content
        passed('usage errors and multiple-program saving preserve existing output')

        for args in [['open', folder / 'missing.obj'], ['open', folder],
                     ['check', '--group', 'todo', '--out', folder]]:
            result = run([BINARY, *args], 1)
            assert result.stderr and not result.stdout
        passed('input and output IO errors are controlled')

        fixture = folder / 'ObjectCli.lean'
        fixture.write_text(FIXTURE)
        lean = [*shlex.split(os.environ.get('LAKE', 'lake')), 'env', 'lean',
                '-DwarningAsError=true', '--run', fixture]
        run([*lean, 'fixtures', folder])
        mutations = {'version.obj': bytes([1]) + content[1:],
                     'spec.obj': content[:2] + bytes([content[2] ^ 1]) + content[3:],
                     'truncated.obj': content[:-1], 'empty.obj': b''}
        for name, value in mutations.items():
            (folder / name).write_bytes(value)
        for name, tag, inner in [('version.obj', 'node', 'badVersion'),
                                 ('spec.obj', 'content', 'spec'),
                                 ('bare.node', 'content', 'spec'),
                                 ('truncated.obj', 'node', None),
                                 ('empty.obj', 'node', None),
                                 ('ill-typed.obj', 'admission', 'illTyped')]:
            result = run([BINARY, 'open', folder / name], 1, cwd=folder)
            assert not result.stdout and result.stderr.startswith('open: ')
            why = json.loads(result.stderr.removeprefix('open: '))
            assert why['_tag'] == tag, why
            if inner:
                assert why['why']['_tag'] == inner, why
            if tag == 'admission':
                assert why['why'] == json.loads((folder / 'admission.json').read_text())
        passed('node, content, and located admission refusals retain their generated JSON')

        run([*lean, 'refuse', obj], 1)
        assert obj.read_bytes() == content
        passed('admission refusal leaves an existing object untouched')

        expected = run([*lean, 'readings'])
        for line in expected.stdout.splitlines():
            reading = json.loads(line)
            args = [BINARY, 'inspect', '--group', 'todo', '--what', reading['name']]
            assert run(args).stdout == reading['text'] + '\n'
            assert run([*args, '--json']).stdout == reading['json'] + '\n'
        passed('four direct readings match the previous Tool query text and JSON')
    print(f'PASS program-object: {checks} CLI control groups')


if __name__ == '__main__':
    main()
