# Receipt: procedures, slice PROC-3 (decisions row 328)

## The one thing to know before merging

A program with a definition block now prints as a TypeScript module and reads back. Each
definition is a constant before the layers and the main declaration. An invocation prints as the
definition's name applied to its request. The round trip is proved through the program interface
(`Api.printModule_roundTrip`), and Effect rc.112 runs four block programs to the machine's exits.

Two parts of the design note are not landed:

- A layer inside a definition body is refused by name, not hoisted.
- A definition's requirement row is printed and not read.

## Base and head

- Base: `ef1412f0` on `refactor/phase1-phase3` (Codex's P2b merged, its claims recorded).
- Head: `a3f6015f` (the slice) and `9edd0db5` (the target selection), on the same branch.

## What landed

**The printer** (`src/Effect4/Codegen/Print.lean`).

- `printDef`: a definition is `const name = (a0: Request): Effect.Effect<A, E, R> =>
  Effect.suspend(() => body)`. The body prints at environment length `1`.
- `printDefs` and the block branch of `printModule`: definitions first, then the layers, then the
  main declaration, all at the block's signature (`Signature.withDefs`). Definitions stand first
  because a layer's body runs when its constant is evaluated, and it may invoke a definition.
- The refusals, each by name:
  - an empty block, which would read back as its main program alone;
  - a layer inside a body (`defs:layer`);
  - an unsafe definition name (`defsNameFault`, checked by `printEntry`): not an export name, the
    main declaration's name, a row's spelling, or a name declared twice.

**The reader** (`src/Effect4/Codegen/Read.lean`).

- `readModule` takes the invocation's operation (`call`, `NativeOp.call` at the native signature).
- The leading constants whose names carry no layer path are the block (`defsPrefix`).
- `readDefHead` reads a header by the checked type reader. `readDefBodies` reads each body from
  its printed suspension.
- The bodies, the main program and the layers read at the block's signature through the block's
  spelling map (`defsSpell`).
- `DefDecl.readable` is the domain of a header: readable columns, an empty requirement row, and a
  name with no layer path.

**The laws.**

- `src/Effect4/Laws/Codegen/Module.lean`:
  - G6 (`readModule_printModule_defs`);
  - the header and block steps (`readDefHead_printDef`, `readDefs_printDefs`);
  - the shape lemma's block case;
  - hoisting keeps a block's declarations (`Eff.hoistAll_defsOf`).
- `src/Effect4/Laws/Codegen/Definitions.lean`:
  - the block's spelling map is lawful (`LawfulSpelling.withDefs`);
  - the native signature's invocation laws (`nativeCalls`);
  - the printer's name check gives the reader's name premises (`defsNamed_of_fault`).
- `src/Effect4/Laws/Api/ModuleReadable.lean`:
  - the readable domain of a block (`blockReadable`);
  - its round trip (`readModule_printModule_defs_readable`);
  - `ModuleEmission.readModule` and `Api.printModule_roundTrip` for either domain.

**The truth corpus** (`harness/truth/Truth.lean`). Four block programs:

- `pDefsTwice`: one invocation;
- `pDefsEven` and `pDefsOdd`: two definitions that invoke each other;
- `pDefsFork`: an invocation inside a fork.

A program with no expression print takes its module from the ordinary producer.

**The battery** (`Test/Codegen/DefinitionsPrint.lean`):

- the printed text of two blocks;
- the readable domain at four programs, with its controls;
- the name bridge applied at a real block;
- the controls of each refusal.

## The theorems and their placement

| Theorem | Concept; claim; role | Requirement |
| --- | --- | --- |
| `readModule_printModule_defs` (G6) | `exact-codecs`; `module-defs-round-trip` (new, proved); compatibility | R8 |
| `LawfulSpelling.withDefs`, `nativeCalls`, `defsNamed_of_fault` | steps of `module-defs-round-trip`; consumer `ModuleEmission.readModule` | R8 |
| `readDefHead_printDef`, `readDefs_printDefs`, `Eff.hoistAll_defsOf` | steps of `module-defs-round-trip`; consumer G6 | R8 |
| `readModule_printModule_defs_readable`, `ModuleEmission.readModule`, `Api.printModule_roundTrip` | the module round trip on the readable domain, with or without a block | R8 |

`readModule_printModule` now states its premise that the hoisted program has no block. The
plain readable domain (`moduleReadable`) says so too. A program with a block is in the other
domain.

## What it does not establish

- That tsgo accepts a printed module, or how rc.112 runs one. The truth lane checks four
  programs, a finite check.
- The layer identity of a layer inside a body: the printer refuses one. Hoisting it needs a
  hoist over a given list of targets and its own success law.
- The reading of a definition's requirement row: a row other than `never` reads as a refusal.
- The reading of a block by the TypeScript reader in `ts/eff`: it refuses each block module by
  name (`unknownHead`), as a file with no oracle.
- A block below the root: the checker and the template table refuse it.

## Commands and results

Run in the main checkout, each through `scratch/lean-slot.sh`, with
`-o ts/eff/node_modules -o harness/truth/node_modules` on every `make`.

| Command | Result |
| --- | --- |
| `lake build Effect4`, `lake build Effect4.Laws` | built |
| `make check-cases` (builds `Test` and runs the gates) | PASS; 855 modules and 98775 declarations checked, semantic and test axioms `[propext, Quot.sound]`; 30 planned goals, none new |
| `make gen-truth` | the four block programs agree with rc.112 on exits, schedules and synchronous exits |
| `make check-truth` | PASS: 80 programs agree, 1 signed divergence; the regenerated modules type-check under tsgo `7.0.0-dev.20260629.1` |
| `make check-ts-reader` | PASS: 489 files, 416 matched, 0 mismatched; 15 refused with no oracle (the four block modules among them); tsgo type-checks `ts/eff`; 742 tests pass |
| `make gen-semantics` | `module-defs-round-trip` proved |
| `make check` | PASS: `check-gen` (every Lean-only group) and `check-docs` (76 documents), after the commit |
| `make check-target` | PASS once the selection names the four block programs: 92 expected, 92 resolved, 0 mismatching; 28 tests pass |

Not run: `make check-ocaml`, `make check-compiler` and the engine cut. The slice changes neither
the program syntax nor the machine, so nothing they read moved.

## Bounded evidence

The truth lane runs four programs on the pinned host, Effect `4.0.0-rc.112`. The battery's
printed texts are finite evaluations. The round trip is the theorem.

## Proposed decisions row

None. Row 328's status records the slice.
