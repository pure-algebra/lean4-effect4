# Receipt: procedures, slice PROC-4 (decisions row 328)

## The one thing to know before merging

An author declares a definition once, and invokes it by name. `Def.of` turns a library operation
into a definition and its invocation in one call. The invocation has the operation's own type,
so existing code takes the invocation in the operation's place unchanged.

The Queue's four operations are definitions too. Its eight scenarios over the definitions answer
as they do over the inline operations. The compiled engine and Effect rc.112 give the same
exits on the runs they hold.

## Base and head

- Base: `93c3430d` on `refactor/phase1-phase3` (PROC-3 and its receipt).
- Head: the commit that carries this receipt, on the same branch.

## What landed

**The authoring surface** (`src/Effect4/Program/Authoring.lean`).

- `DefSrc`: a definition's name, its parameters with their names and types, its declared row,
  and its body as a function of its parameters' terms.
- The parameters are one request: none is `unit`, one is its own type, and more are nested
  pairs (`requestTy`, `requestParts`, `requestOf`).
- `Module.defs`, and the environment's definition names.
- `elaborateModule` places the block at the root when a module declares a definition
  (`elaborateTree`). Authoring elaboration reads each body at the closed scope with one minted
  name for its request, at its path in the block.
- `Def.invoke` resolves a name to the definition's index. An undeclared name refuses at the
  site, by name (`Reason.unboundDef`), and a name declared twice refuses the module
  (`Reason.duplicateDef`). The two reasons are appended, and the `derived` group is regenerated.

**The deep method** (`src/Effect4/Program/Authoring/Defs.lean`).

- `Def.of name params answer op` gives a `Defined F`. Its `src` goes in a module's `defs`, and
  its `call` has the operation's type `F`.
- `Params` reads the arity off the operation's type, so an operation of any arity needs no code
  of its own.

**The Queue as definitions** (`src/Effect4/Modules/Queue/Defs.lean`).

- `takeD`, `offerD`, `pollD` and `sizeD`, each one call of `Def.of` over the operation of
  `Ops.lean`.
- `defs A suffix` lists the four, and a suffix gives a second message type its own names.

**The faces.**

- The engine's fixture `ocaml/engine/test/queue/queue-defs.txt` holds R1, R4, R2 and R5 over the
  definitions. Its writer is `write.lean`, and its binding is `Test/Program/QueueEngine.lean`.
- `test_queue.ml` runs these as it runs `queue.txt`, and Q5 checks that each answers the inline
  run's exit from another program.
- The truth lane's `pQueueDefs` is R4 over the definitions. The target lane selects it.

## Measured again (`Test/Program/QueueDefs.lean`, finite evaluations)

The least fuel at which the ordinary run has an exit:

| Scenario | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| inline operations | 119 | 73 | 138 | 98 | 133 | 131 | 75 | 151 |
| definitions | 123 | 75 | 142 | 101 | 136 | 135 | 76 | 155 |

Each invocation that a run reaches is one more step. The exits are equal in all eight
scenarios.

The TypeScript printed module of R1, which offers twice and takes twice:

| Form | Characters |
| --- | --- |
| inline operations | 23189 |
| definitions: `take` 7549, `offer` 4325, `poll` 2549, `size` 583, the main declaration 1493 | 16499 |

A definition costs its text once, and a use is one call. A module that declares all four
definitions pays for `poll` and `size` even where it does not use them. So R7, which takes once,
prints 8526 characters inline and 16484 over the four definitions.

## The theorems and their placement

No new theorem. The block's laws of PROC-1 to PROC-3 apply to each program the surface builds:

- the module check and admission (G1, G2);
- M5's invocation arm (G3) and the frame machine's agreement (G4);
- the module round trip (G6).

The runs over the two forms are finite controls of goal G7, an invocation and its inlining
under decisions row 329's relation. G7 is open.

## What it does not establish

- That an invocation and its inlining have one observation (G7). The eight scenarios, the
  engine's four runs and the truth lane's one run are finite checks.
- `Package.defs`. A package is a host library's rows and services. A composed module offers
  its definitions as a list that a module places, and `Package` keeps its decidable equality.
- A command `eff_def` beside `eff_rows`. `Def.of` does the work that the command would call.
- The address table and the focus inside a definition's body. The focus step does not enter a
  block (`childEnv` answers `none` at `Eff.defs`).

## Commands and results

Run in the main checkout, each through `scratch/lean-slot.sh`, with
`-o ts/eff/node_modules -o harness/truth/node_modules` on every `make`.

| Command | Result |
| --- | --- |
| `python3 scripts/generate.py --only derived`, then `eff`, `wire`, `ts` | `RefusalsDerived.lean` regenerated; the other groups byte-identical |
| `python3 scripts/generate.py --only fixtures` | `queue-defs.txt` written; `queue.txt` unchanged |
| `make check-cases` (builds `Test` and runs the gates) | PASS; 858 modules and 98937 declarations, semantic and test axioms `[propext, Quot.sound]`; 30 planned goals, none new |
| `make gen-truth`, `make check-truth` | PASS: 81 programs agree, 1 signed divergence; `pQueueDefs` agrees with `pQueueFull`'s exit |
| `make check-target` | PASS: 93 expected, 93 resolved, 0 mismatching |
| `make check-ts-reader` | PASS: 490 files, 416 matched, 0 mismatched; 742 tests pass |
| `dune test engine/test/queue` (through `opam exec --switch=effect4`) | 92 checks, 0 failures, Q5 included |
| `make check-ocaml` | PASS |

## Bounded evidence

- The scenarios run on one schedule each, at a fixed fuel.
- The engine runs four programs on its own drive loop.
- The truth lane runs one program on the pinned host, Effect `4.0.0-rc.112`.

## Proposed decisions row

None. Row 328's status records the slice.
