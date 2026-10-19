#!/usr/bin/env python3
"""Run the scheduler model test stm_admit N copies at a time, for R rounds, and count the runs
whose green parallel test P1 failed.  The receipt's finding outside the brief (stm_admit-p1.txt)
rests on these counts.

    python3 docs/research/2026-10-18-slices/w2-engine-mutants/stm_load.py EXE OUTDIR N R

EXE is a built `ocaml/_build/default/engine/test/stm/stm_admit.exe` (build it first with
`opam exec --switch=effect4 -- dune build ./engine/test/stm/stm_admit.exe` in `ocaml/`).
Each run's output goes to OUTDIR/r<round>_<copy>.out.  N = 1 runs the copies one at a time;
a larger N loads the host with the copies themselves.
"""
import subprocess
import sys
import time
from pathlib import Path

P1_FAILED = 'Test P1 E4_sched admission, two client domains failed'


def main():
    exe, out, n, rounds = Path(sys.argv[1]), Path(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    out.mkdir(parents=True, exist_ok=True)
    nonzero, p1, total = 0, [], 0
    start = time.time()
    for r in range(rounds):
        running = []
        for i in range(n):
            path = out / f'r{r}_{i}.out'
            f = path.open('w')
            running.append((subprocess.Popen([str(exe)], cwd=exe.parent, stdout=f,
                                             stderr=subprocess.STDOUT), f, path))
        for proc, f, path in running:
            code = proc.wait()
            f.close()
            total += 1
            nonzero += code != 0
            if P1_FAILED in path.read_text():
                p1.append(path.name)
    print(f'{total} runs, {n} at a time: {nonzero} exited non-zero, {len(p1)} with P1 failed '
          f'({", ".join(p1) or "none"}); {time.time() - start:.0f} s')
    return 0


if __name__ == '__main__':
    sys.exit(main())
