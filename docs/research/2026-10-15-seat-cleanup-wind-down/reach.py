"""Census probe (seat CLEANUP, S4, 2026-10-15): the Lean modules of the tool estate that no runner
reaches, measured as K4 measured Conform's (docs/research/2026-10-15-lowering-state/probes/
conform-reach.py), over every tool library.

A runner is a library root (`Effect4`, `Effect4.Laws`), the batteries' roots (`Test/All.lean`,
`Test/Slow.lean`), a `lean_exe` root of `lakefile.toml`, and every `.lean` file that the
`Makefile`, a script, the CI workflow, a fixture writer or an authority document names by path
or by module. A module is reached when a runner's import closure holds it. The unreached
modules of the globbed tool libraries (`Tools`, `Drivers`, `TestSupport`, `Conform`,
`ProofGraph`, `OCaml5`, `Effect4Gen`) are printed with their line counts and every other file
that names them (a docstring, a register row), so a reader can judge each one.

    python3 docs/research/2026-10-15-seat-cleanup-wind-down/reach.py            # tools/ and src/OCaml5
    python3 docs/research/2026-10-15-seat-cleanup-wind-down/reach.py --hosts    # harness/, apps/, ocaml/
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
from lib.lean_imports import header_imports  # noqa: E402

BASES = ['src', 'tools', '.']


def module_path(mod):
    for base in BASES:
        p = ROOT / base / (mod.replace('.', '/') + '.lean')
        if p.exists():
            return p
    return None


def module_of(path):
    rel = path.relative_to(ROOT).as_posix()
    for base in ['src/', 'tools/']:
        if rel.startswith(base):
            rel = rel[len(base):]
            break
    return rel.removesuffix('.lean').replace('/', '.')


def closure(paths):
    seen, work = set(), list(paths)
    while work:
        p = work.pop()
        if p in seen or not p.exists():
            continue
        seen.add(p)
        for m in header_imports(p.read_text(errors='ignore')):
            q = module_path(m)
            if q is not None:
                work.append(q)
    return seen


def text_of(paths):
    return '\n'.join(p.read_text(errors='ignore') for p in paths if p.is_file())


# Runner texts: the Makefile, the scripts, CI, the authority documents and every non-Lean
# program the gates run (harness, apps, ocaml tools and fixture writers).
authority = [ROOT / 'README.md', ROOT / 'AGENTS.md', ROOT / 'docs/STATE.md', ROOT / 'docs/ARCHITECTURE.md',
             ROOT / 'docs/GENERATED.md', ROOT / 'docs/DESIGN-BASIS.md', ROOT / 'docs/DESIGN-ISSUES.md',
             ROOT / 'docs/RUNTIME-COVERAGE.md', ROOT / 'ocaml/README.md', ROOT / 'lakefile.toml',
             *(ROOT / 'docs/core').glob('*.md')]
scripts = [p for p in (ROOT / 'scripts').rglob('*') if p.is_file()]
ci = list((ROOT / '.github').rglob('*.yml'))
hosts = [p for d in ['harness', 'apps', 'ts/eff', 'tools', 'ocaml', 'Test/contracts', 'docs/site'] for p in (ROOT / d).rglob('*')
         if p.is_file() and (p.suffix in {'.py', '.sh', '.ts', '.mjs', '.json', '.md', '.ml', '.c', '.h', '.html'}
                             or p.suffix == '' or (p.suffix == '.lean' and p.parent.name in {'session', 'schema-codec'}))
         and 'node_modules' not in p.parts and '_build' not in p.parts]
runner_text = text_of([ROOT / 'Makefile', *scripts, *ci, *authority, *hosts])

# Runners named by path or by module in the runner texts.
lean_files = [p for base in ['src', 'tools', 'Test', 'harness', 'apps', 'ocaml'] for p in (ROOT / base).rglob('*.lean')
              if '.lake' not in p.parts and '_build' not in p.parts]
named = set()
for p in lean_files:
    rel = p.relative_to(ROOT).as_posix()
    if rel in runner_text or module_of(p) in runner_text:
        named.add(p)

lake = (ROOT / 'lakefile.toml').read_text()
exe_roots = [module_path(m) for m in re.findall(r'root\s*=\s*"([^"]+)"', lake)]
roots = [module_path('Effect4'), module_path('Effect4.Laws'), ROOT / 'Test/All.lean', ROOT / 'Test/Slow.lean',
         *(p for p in exe_roots if p is not None), *named]
reached = closure([p for p in roots if p is not None])

# The tool estate: every Lean file under tools/ and src/OCaml5.
if '--hosts' in sys.argv:
    estate = sorted(p for d in ('harness', 'apps', 'ocaml') for p in (ROOT / d).rglob('*.lean')
                    if 'node_modules' not in p.parts and '_build' not in p.parts)
else:
    estate = sorted([p for p in (ROOT / 'tools').rglob('*.lean')] + [p for p in (ROOT / 'src/OCaml5').rglob('*.lean')])
unreached = [p for p in estate if p not in reached]
all_text = text_of([p for p in ROOT.rglob('*') if p.is_file() and p.suffix in {'.lean', '.md', '.py', '.sh', '.json', '.toml', '.ml', '.ts'}
                    and not any(x in p.parts for x in ('.lake', 'node_modules', '_build', 'research', 'vendor'))])
total = 0
for p in unreached:
    rel = p.relative_to(ROOT).as_posix()
    n = sum(1 for _ in open(p, errors='ignore'))
    total += n
    mod = module_of(p)
    mentions = [q.relative_to(ROOT).as_posix() for q in ROOT.rglob('*')
                if q.is_file() and q.suffix in {'.lean', '.md', '.py', '.sh', '.toml'}
                and not any(x in q.parts for x in ('.lake', 'node_modules', '_build', 'vendor'))
                and q != p and (mod in q.read_text(errors='ignore') or rel in q.read_text(errors='ignore'))]
    print(f'{n}\t{rel}\tnamed by: {", ".join(sorted(mentions)[:6]) or "nothing"}')
print(f'unreached: {len(unreached)} of {len(estate)} tool modules, {total} lines')
