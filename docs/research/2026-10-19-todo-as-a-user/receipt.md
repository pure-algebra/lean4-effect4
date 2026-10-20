# The to-do as a user's project: receipt

Status: receipt, 2026-10-19. The seat for `plan.md`. The findings are `findings.md` beside this
note.

## 1. The one thing to know

The six phases ran, and the loop closes from outside the library. 336 lines of authored Lean
became a Lean run. Lowered to OCaml by the LCNF route, they run on the installed kit and answer
the same eleven requests byte for byte. Printed as Effect TypeScript syntax, they type-check under tsgo 7, and the printed
service runs on Effect 4.0.0-rc.112 under Bun with the same eleven answers. The library changed
nothing. Three frictions a user cannot solve alone remain. The hand service key and the host
written as string-named functions belong to item 9. The lowering command copied from a generated
header, with no text in lowered code, is new.

## 2. The commits

The project, `/Users/pooks/Dev/effect4-todo`, branch `main`, never pushed:

| Commit | What |
| --- | --- |
| `4dc6d1c` | the Lean: the application, the host, the script, the print, the main, the README |
| `c1a2752` | the native side: `ocaml/todo_gen.ml` and its manifest, the dune files, the main |
| `1211bca` | the TypeScript side: the printed module, the host configuration, the link |
| `275fc1b` | the printed service run on Effect under Bun (`ts/run.ts`), the decoder of the Lean run's lines (`ts/lean-lines.ts`), the README's two steps |

The library, `refactor/phase1-phase3` at `afc14d86f`: `503744175` adds `findings.md` and this
receipt, force-added, by explicit paths, and a second commit adds the Bun run to both. No other
file of the library changed.

The commits carry `Co-Authored-By: Claude Fable 5.1`, the model that did the work; the brief's
line named Opus 5.5.

## 3. The commands and their results

Every Lean command ran through `python3 /private/tmp/seams-lean-one.py lake …` from inside the
project. Times are `/usr/bin/time -p` wall clock.

| Phase | Command | Result |
| --- | --- | --- |
| setup | `git init`; `lean-toolchain` = `leanprover/lean4:v4.33.1`; `cp -c -R <library>/.lake/packages .lake/packages` | 1.57 s, 552 MB, six packages |
| 1 | `lake build` | first 3.03 s, failed on a docstring before `eff_record` (findings 3.7); then 3.30 s, 219 jobs, nothing of the library rebuilt |
| 2 | `lake build todo`; `lake exe todo` | 3.75 s; eleven lines, each the specification's answer |
| 2 | `lake exe todo --json` | eleven JSON lines, `.work/run-lean.json` |
| 3 | `lake exe lcnfgen --out ocaml/todo_gen.ml --import Todo --cap 4000 --open Eff_types --open-types <37 names> Todo.Host.repository Todo.Host.initial Todo.Host.script Todo.Host.programOf Todo.Host.rows Todo.Host.resultVal` | 2.07 s; closure 367 of 4000; `Ml.checkModule: PASS`; 6,305 lines |
| 3 | the same with `Todo.Host.line` | failed: six externs of text building (findings 3.2) |
| 3 | the same with `Todo.Host.build` added, into `.work/` | 1,031 nodes, 17,913 lines (findings 3.10) |
| 4 | `OCAMLPATH=<library>/ocaml/_build/install/default/lib opam exec --switch=effect4 -- dune build ./todo_native.exe` | 1.23 s |
| 4 | `./_build/default/todo_native.exe`; `diff` against the Lean JSON | 0.04 s; `SAME` |
| 5 | `lake exe todo ts ts/todo.gen.ts ../../lean4-effect4/harness/truth/prelude.ts` | 0.42 s, 85 lines |
| 5 | `tsgo --noEmit -p tsconfig.json` (7.0.0-dev.20260629.1) | without the key: 6 errors (findings 3.3); with it: exit 0 |
| 5 | `bun ts/run.ts` (Bun 1.4.2, effect 4.0.0-rc.112) | 0.13 s; eleven lines, each the specification's answer |
| 5 | `lake exe todo --json \| bun ts/lean-lines.ts \| diff - <(bun ts/run.ts)` | `SAME` |
| 6 | `wc -l` over the tree | 7,437 lines: 336 Lean, 6,832 generated, 269 hand outside Lean |

The library's gates did not run: no library file changed. `make check-full`, `lake build Test`,
`make build` and `make gen-semantics` were not run.

## 4. What did not finish

- No repository written in OCaml ran against the lowered host record. The native run's
  repository is the lowered Lean one, which the brief's Phase 4 allows. The TypeScript run's
  repository is hand-written.
- The cost of `require` by Git at a pinned commit, which the plan measures once, was not measured.
- The `.work/` folder of the project, with the logs, the no-key print and the checker measurement,
  is ignored, not committed.
- The findings may reorder `coherence.md` §9.1; this receipt proposes no row. Findings 3.1 and
  3.2 ask for new items, and 3.3, 3.4 and 3.7 add evidence to item 9.
