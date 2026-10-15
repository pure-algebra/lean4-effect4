"""Time every dune test executable of the estate, run from its build directory as dune runs it."""
import re, subprocess, time, pathlib
root = pathlib.Path('/Users/pooks/Dev/lean4-effect4/ocaml')
files = subprocess.run(['git', 'ls-files'], cwd=root, capture_output=True, text=True).stdout.split()
for f in files:
    if not f.endswith('/dune') and f != 'dune':
        continue
    text = (root / f).read_text()
    d = str(pathlib.Path(f).parent)
    for m in re.finditer(r'\(test\s*\(name\s+([a-z_0-9]+)\)', text):
        t = m.group(1)
        cwd = root / '_build/default' / d
        exe = cwd / f'{t}.exe'
        if not exe.exists():
            print(f'MISSING {d}/{t}'); continue
        s = time.time()
        r = subprocess.run(['opam', 'exec', '--switch=effect4', '--', f'./{t}.exe'], cwd=cwd,
                           capture_output=True, text=True)
        out = (r.stdout + r.stderr).strip().splitlines()
        print(f'{time.time()-s:7.2f} s rc={r.returncode} {d}/{t} :: {out[-1][:90] if out else ""}', flush=True)
