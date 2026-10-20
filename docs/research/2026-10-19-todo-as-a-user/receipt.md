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

## 5. After move G: the key names, 2026-10-20

**The one thing to know:** move G breaks two files of the project at `689b0a9`. `typedJson`
now passes the key names, and the README's lowering command writes `ocaml/todo_gen.ml` again.

The project's `main` moves from `689b0a9` to `6be67a1`. Every run read the library at
`6d12bc246` on `refactor/phase1-phase3`. The commit changes three files of the project:

- `Todo/Host.lean`: `typedJson` passes the key names, and its docstring says so.
- `ocaml/todo_gen.ml` and `ocaml/closure-todo_gen.tsv`: written again by the README's lowering
  command.

The line a user now writes gives the codec the module's key names first:

```lean
Ty.encode (nativeSignature b.table).keyNames (.exitOf b.ty.answer b.ty.error) (Machine.exitImage.toVal e)
```

`nativeSignature` (`src/Effect4/Program/Native.lean`) carries the names that the program's rows
give their keys. The faces probe passes them the same way, in its `typedJson`
(`docs/research/2026-10-19-schema-as-the-carrier/probe/Faces.lean`).

The native side breaks too. Move G gives `Defect.missingService`
(`src/Effect4/Machine/Alphabets.lean`) its key. The lowered file still matched the constructor
without it. The lowering reaches the defect through `Machine.exitImage` (the same file), which
the root `Todo.Host.resultVal` calls through `exitVal`. The new closure grows from 367 to 373
nodes, with `Env.serviceKeyImage` (`src/Effect4/Machine/ContextMap.lean`) among them.

Each Lean command ran through `python3 /private/tmp/seams-lean-one.py` from inside the project,
in the README's order. Each time is the wall clock of `/usr/bin/time -p`.

| Command | Result |
| --- | --- |
| `lake build` at `689b0a9`, the red control | refused at `typedJson`: `.exitOf` met the expected type `KeyNames`; 10.48 s |
| `lake build` | passed: 249 jobs, 11.19 s; `Todo.Host` and `Todo` rebuilt, nothing of the library |
| `lake exe todo` | eleven lines, equal to those of the `689b0a9` binary; 1.80 s |
| `opam exec --switch=effect4 -- dune build ./todo_native.exe` before the lowering, the red control | refused: `Defect.MissingService` expects 1 argument |
| the README's `lake exe lcnfgen …` | closure 373 of 4000; `Ml.checkModule: PASS`; 6,394 lines; a second run wrote the same bytes |
| the README's `dune build ./todo_native.exe`, then the native run against `lake exe todo --json` | exit 0, 1.14 s; `SAME` |
| `lake exe todo ts` into a scratch folder | both files equal `ts/todo.gen.ts` and `ts/todo.surface.gen.ts` byte for byte |
| `lake exe todo --json \| bun ts/lean-lines.ts \| diff - <(bun ts/run.ts)` | `SAME` |
| `lake exe todo --typed \| diff - <(bun ts/run.ts --typed)` | `SAME` |
| each comparison with one Lean line altered, the red controls | `diff` exit 1 |

No typed line differs between the faces. The eleven typed lines also equal those of the
`689b0a9` binary, built before the move.

- **Tested:** the three comparisons, a finite probe of eleven requests on one machine. The
  TypeScript face is host-only: it ran under Bun 1.4.2 on `effect` 4.0.0-rc.112.
- **Reproduced:** the lowered file and the printed module, each by a byte comparison against a
  fresh producer run.

The comparisons do not reach the defect's encoding. No request of the script dies, so the key
names change no line here. `tsgo` did not run again, since the printed files and the prelude did
not change. No library file changed but this receipt, so no library gate ran and no axiom output
applies.
