# Receipt: procedures, slices PROC-1 and PROC-2 (decisions row 328)

## The one thing to know before merging

A program may now hold a definition block at its root, and every layer admits and runs it.
`typeOfProgram` is the whole module's check, so admission, the program interface and the session
take a block. M5's invocation arm is proved (`call_arm`), not vacuous. The TypeScript printer still
refuses a block by name: printing is slice PROC-3.

## Base and head

- Base: `434f9c03` (decisions rows 328 and 329), merged with `refactor/phase1-phase3` at `75529f68`
  (Codex's P3 and UNGUARD), in `2d66b208`.
- Head: branch `claude/procedures` (worktree `.claude/worktrees/procedures`), the commit that
  carries this receipt; its code is `5c18287c`'s.

## What landed

**PROC-1, the program syntax and the typing.**

- The appends: `Eff.defs`, the `DefDecl` declaration, and `NativeOp.call`, with their wire tags,
  their binder row and the generated groups (`src/Effect4/Program/Eff.lean`,
  `src/Effect4/Program/Native.lean`, `tools/Effect4Gen/wire-tags.json`).
- The block's signature `Signature.withDefs` and the whole module's check `Checker.checkModule`
  (`src/Effect4/Program/Definitions.lean`). `typeOfProgram` and `Api.explain` read it
  (`src/Effect4/Program/Typing.lean`, `src/Effect4/Api.lean`).
- Formation reads a definition's declared columns (`Formation.declAnnotations`,
  `src/Effect4/Program/Formation.lean`).
- An extension keeps which operations are invocations (`SigExtends.callOf`,
  `src/Effect4/Laws/Program/Signature.lean`).

**PROC-2, the machine and M5's arm.**

- `compileEff`, `suspendBodyAt` and `denoteR` arms for the block and the invocation
  (`src/Effect4/Program/Compile.lean`, `src/Effect4/Laws/Program/DenoteR.lean`).
- The invocation's environment is built from the point's own carrier (`p.env.take 0 ++ [v]`). So
  the OCaml engine keeps it in its environment type, as for `Point.layerBuild`'s empty one.
- The source's signature carries the program's block (`ProgramSource.signature`,
  `src/Effect4/Laws/Program/Typed/Admission.lean`). `SourceWF` carries the references' formation
  and the block's typed bodies, and the load discharges both from the checker's verdict
  (`sourceWF_of_typeOf`, `src/Effect4/Laws/Program/Typed/Assembly.lean`).
- The OCaml faces: the estate's encoders and the engine's view (`src/OCaml5/Eff/Emit.lean`,
  `src/OCaml5/Eff/Goldens.lean`, `ocaml/engine/e4_program.ml`). The engine cuts request the
  declaration in full (`ocaml/gen/roots.json`).
- The TypeScript faces: the mirror's generator and `ts/eff`'s hand switches
  (`tools/Drivers/TsGen.lean`, `ts/eff/read.ts`, `ts/eff/ingest/ck.ts`,
  `ts/eff/ingest/check-coverage.ts`).

## The theorems and their placement

| Theorem | Path | Concept; claim; role | Requirement |
| --- | --- | --- | --- |
| `defs_conservative` (G1) | `src/Effect4/Laws/Program/Definitions.lean` | `initial-algebras-folds`; `defs-conservative`; compatibility | R2 |
| `invoke_hasTy` (G2) | same | `initial-algebras-folds`; `invocation-rule`; compatibility | R1 |
| `checkModule_sound`, `checkModule_complete` (G2) | same | `initial-algebras-folds`; `module-check`; compatibility | R1 |
| `call_arm` (G3) | `src/Effect4/Laws/Program/Typed/Denotation.lean` | `residual-program-typing`; `invocation-arm`; fundamental property, M5's arm | M5 → M6 → M7 |
| `intro_call` and the agreement's invocation case (G4) | `src/Effect4/Laws/Program/Intro/Sequential.lean`, `src/Effect4/Laws/Program/Agreement.lean` | `translation-simulation`; `run-eq-ref` | R8 |

The steps:

- `moduleHasTy_ext` and `typeOfProgram_ext`: the module judgment along an extension.
- `typeOfProgram_closed` for a module: an admitted program with a block has closed types.
- `bodiesTyped_of_typeOf`, `mainChecked_of_typeOf` and `rootCode_typed`: the load's start, with or
  without a block.
- `Signature.withDefs_nil` and `ProgramSource.signature_of_defsOf_nil`: a program with no block
  is typed at its tables' signature.

Each step names its consumer in its docstring.

## What it does not establish

- The termination of a recursive definition, or progress and liveness. A definition that invokes
  itself without end runs to the budget's frontier, which is a live frontier and no failure.
- That a declared row is inhabited (decisions row 127), or any generic definition (goal G8).
- A printed block, or its reading back: the printer refuses `defs` by name (slice PROC-3).
- The authoring surface for definitions, or a composed module's operations as definitions (PROC-4).
- The laws of the block's handler (G5) and the inlining law (G7, under row 329's relation).
- M7 at a non-empty row table (DI-57): M7 stays at the empty row table, as before.

## Commands and results

Run in the worktree at `5c18287c`, each through `scratch/lean-slot.sh`, with
`-o ts/eff/node_modules -o harness/truth/node_modules` on every `make`.

| Command | Result |
| --- | --- |
| `lake build Effect4.Laws` | built |
| `lake build Test` | built; the module and axiom gate checked 852 modules and 97326 declarations, semantic and test axioms `[propext, Quot.sound]`; 30 planned goals, none new |
| `python3 scripts/generate.py --only lcnf`, then `eff`, `wire`, `cas`, `ts` | PASS, committed |
| `make gen-semantics` | committed; claims `defs-conservative`, `invocation-rule`, `module-check` and `invocation-arm` proved |
| `make check-ts-reader` | PASS: 416 of 481 files match the oracle, 0 mismatched; tsgo `7.0.0-dev.20260629.1` type-checks `ts/eff`; 742 tests pass |
| `make check-ocaml` | PASS: `dune build`; the eff, gen and clock tests; the engine's tests, whose differential decodes all 83 goldens and runs each on both instances, equal (the four with a block included); the seam check |
| `make check-compiler` | PASS |
| `make check-cases` | PASS after the re-pin: 237 of 237 subjects |
| `make check-native` | PASS |
| `make check` | PASS: the roots, the proof-style ratchet, `check-gen` (every Lean-only group), `check-tsgo`, `check-docs` (76 documents) |

Not run: `make check-truth`, `make check-target` and the rest of `make check-full`, which run at the
owner's sweep. No program of the truth corpus has a block, and the printer refuses one.

## Bounded evidence

The runs in `Test/Program/DefinitionsControls.lean` are finite evaluations at fixed budgets: one
invocation, mutual recursion, recursion to the frontier and an invocation inside a fork. The OCaml
estate's golden corpus holds four programs with a block, two typed and two refused. The compiled
engine runs each on both instances. That is a finite check of the engine on four
programs; the frame machine's agreement with the reference (G4) is the theorem.

## Proposed decisions row

Row 328's status: slices PROC-1 and PROC-2 landed, G1 to G4 proved. The remaining slices are
PROC-3 to PROC-5, in the note's order.
