#!/usr/bin/env python3
"""Compile a probe against the pinned worktree's build; write only beside this script."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / '_build/default'
LIBS = ['lcnf/effect4_lcnf', 'clock/effect4_clock', 'eff/effect4_eff',
        'gen/effect4_closure', 'gen/effect4_gen', 'engine/bytes/effect4_bytes',
        'engine/effect4_engine', 'engine/cas/effect4_engine_cas',
        'engine/kit/effect4_kit']

def compile_probe(source, packages='zarith,yojson,unix,threads'):
    source = Path(source).resolve()
    target = source.with_suffix('.exe')
    cmd = ['opam', 'exec', '--switch=effect4', '--', 'ocamlfind', 'ocamlopt',
           '-thread', '-package', packages, '-linkpkg', '-g']
    for name in LIBS:
        parent, lib = name.rsplit('/', 1)
        for folder in [BUILD / parent, BUILD / parent / ('.' + lib + '.objs/byte'),
                       BUILD / parent / ('.' + lib + '.objs/native')]:
            cmd += ['-I', str(folder)]
    cmd += [str(BUILD / (name + '.cmxa')) for name in LIBS]
    cmd += [str(source), '-o', str(target)]
    subprocess.run(cmd, check=True, cwd=ROOT)
    return target

if __name__ == '__main__':
    exe = compile_probe(sys.argv[1])
    raise SystemExit(subprocess.run([str(exe), *sys.argv[2:]], cwd=ROOT).returncode)
