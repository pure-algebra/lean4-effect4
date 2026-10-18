# Receipt: seat 3, export classes and the public-name manifest

Seat 3 of wave 1 (`wave1-briefs.md`, "Seat 3"). Branch `seat/w1-names`, worktree
`/Users/pooks/Dev/wt-w1-names`.

## The one thing to know before merging

After this branch, `make gen-lcnf` holds every path of `ocaml/gen/public-names.tsv` at version 0.
A merged change that moves or drops a public path makes regeneration refuse, and nothing is
written. Such a change renames or removes a public root of `Api_gen`, or a program type's
constructor or field, or reclassifies a root. Seat 1's Tool and Kit work reaches several. The
remedy is to keep the path, or to raise `facade.version` in `ocaml/gen/roots.json`, which declares
a break. The recipe is format v3 too: another branch's edit in the v2 form (`roots`) is refused,
so the coordinator moves it into a class list.

## Base and head

- Base: `4a81cc034`.
- Slice 3a: `e9b21a9a1`. Slice 3b: `3f75fba32`.
- Head: the commit that adds this receipt, the tip of `seat/w1-names`.

## Slice 3a: typed export classes (`e9b21a9a1`)

Files (18):
- sources: `src/OCaml5/Lcnf/Export.lean` (new), `src/OCaml5/Lcnf/Gen.lean`,
  `src/OCaml5/Tools/LcnfGen.lean`, `src/OCaml5.lean`, `ocaml/gen/roots.json`;
- checks and documents: `scripts/check-export-classes.py` (new), `Makefile`, `ocaml/README.md`;
- generated: `ocaml/gen/api_gen.ml` and `.mli`, `ocaml/engine/api_engine.ml` and `.mli`,
  `ocaml/gen/closure-api_gen.tsv`, `ocaml/gen/closure-api_engine.tsv`;
- generated, header line only: `todo_gen.ml`, `ctors_gen.ml`, `modeled_gen.ml`, `rocq_gen.ml`.

What landed:
- `ocaml/gen/roots.json` is format `effect4-lcnf-roots-v3`. Each root of an artifact sits in one of
  four lists: `public`, `linkage`, `internal`, `coverage`. A top-level `facade.module` names the
  public facade's module, `Effect4`.
- `src/OCaml5/Lcnf/Export.lean` (new) reads the recipe into `ExportPlan` and checks it
  (`ExportPlan.check`, `readChecked`). A `CheckedPlan` carries the two finite checks.
- `src/OCaml5/Lcnf/Gen.lean`: `recipeArgvs` makes no artifact from a refused plan. `argvOf` takes
  the classes from the checked plan. A header now carries `--coverage`, `--internal`, `--linkage`,
  then the public roots. `run` exports `public` and `linkage` roots and hides the other two.
- `scripts/check-export-classes.py` (new), run by `make check-ocaml`: three exported roots link,
  and four hidden roots are unbound.

The frozen classes:

| Artifact | public | linkage | internal | coverage |
| --- | --- | --- | --- | --- |
| `Api_gen` | 93 | 17 | 0 | 41 |
| `Api_engine` | 0 | 12 | 2 (`Scope.make`, `Scope.fork`) | 6 |
| `Todo_gen`, `Ctors_gen`, `Modeled_gen`, `Rocq_gen` | 0 | 14, 46, 4, 2 | 0 | 0 |

The classification came from a census of the hand OCaml (`git ls-files`, every file whose first
line is not a `GENERATED` header), then from the build. The 17 linkage roots of `Api_gen` are the
roots that hand code calls and that are no public promise. Their callers:
- the engine's instance: `Api.load`, `Program.interpOf`, `RunMachine.finished`, …;
- the Rocq lane: `Decision.decide`, `evalTerm`, `Tree.Eval.*`, `syncOpStep`, `Stores.empty`,
  `NativeOp.syncOpOf`;
- the kit: `errOf`;
- the G0 smoke: `HandleKind.byte`, `NativeAtom.eval`.

 They match the stopped 1.1 attempt's linkage list
(`8e10b6c29`, branch `seat/p1-gen-1.1-wip`) less its compiler-made specialisation, which no hand
code calls at the base. No hand code calls `Api_engine`'s six coverage roots or its two internal
roots, so its interface hid them and the whole workspace still built.

The plan checker's rules, each with its control in `Export.lean`:
- a root under two classes of one artifact is refused, naming both classes (`contradictory`);
- a root listed twice under one class is refused (`duplicate`);
- a root public in two artifacts, or public roots in two artifacts, are refused (`publicTwice`,
  `publicSplit`);
- an entry key that is neither an option nor a class is refused (`unknownKey`, a misspelt
  `publik`);
- a nominal root must be exported (`nominalHidden`);
- `facade_resolves`: every root a consumer may see is a row of its facade that resolves to itself.
  Red control: a client spelling that sends `A.aB` and `A.a_b` to one name leaves `A.a_b`
  unresolved;
- `public_excludes_coverage`: no coverage-only root reaches the public facade. Red control: a
  hand-built plan whose coverage root names the facade as a consumer is refused.

The same Lean name in two artifacts is two specialised nodes (R6.1), so the checker allows
`Effect4.Api.run` public in `Api_gen` and linkage in `Api_engine`.

What moved in generated files:
- `api_engine.mli` lost eight values: `drive_state`, `program_admit`, `program_node_child`,
  `run_fiber_make`, `scope_fork`, `scope_make`, `settled`, `step_decision_state`. Its type
  declarations are the same set.
- `api_gen.mli` keeps its values; 47 lines reorder (the same lines as a multiset).
- The closure walk now starts class by class: public, linkage, internal, coverage. So
  `api_gen.ml` (88 lines) and `api_engine.ml` (3,138 lines) reorder their declarations, and their
  closure manifests reorder rows.
- Lane interfaces are unchanged; lane implementations change only in their header line.
- No wire shape and no digest moved.

Commands and results for 3a:

| Command | Result |
| --- | --- |
| `python3 /private/tmp/seams-lean-one.py lake build OCaml5 lcnfgen` | 176 jobs, success |
| `python3 /private/tmp/seams-lean-one.py make gen-lcnf` | `PASS generate`, 1:43 |
| `opam exec --switch=effect4 -- dune build` (in `ocaml/`) | success; only the base's warning 69 lines |
| `python3 scripts/check-export-classes.py` | `PASS: 3 exported roots compile; 4 hidden roots are unbound` |
| `python3 /private/tmp/seams-lean-one.py make batteries-touched BASE=4a81cc034` | 1,702 of 1,703 jobs; `Test.Run.LiveContract` fails, see "Found at the base" |
| `python3 /private/tmp/seams-lean-one.py make check-ocaml` | exit 0, `PASS ocaml: recorded 142f9199cc56`, 5:16; `gen-check: PASS` |

Axiom output for 3a (`#axiom_audit OCaml5.Lcnf.Export OCaml5.Lcnf.Gen OCaml5.Tools.LcnfGen`,
through `lake env lean`): 32 of 356 declarations reach `Classical.choice`. Every path enters
through a toolchain constant: `Lean.Json`, `Lean.Json.parse`, `String.instOrd`,
`Lean.Name.instToString`, `System.FilePath.fileStem`. At the base, the same command over
`OCaml5.Lcnf.Gen` and `OCaml5.Tools.LcnfGen` reports 20 of 124. Those 20 are the same
declarations of those two modules now. `Export` adds 12: its recipe reader and its controls. Its
plan functions (`rootsFor`, `facade`, `onlyCoverage`, `unresolved`, `refusals`, `check`) reach no
axiom outside `[propext, Quot.sound]`. `OCaml5` is no module of the axiom gate (`Effect4.*`,
`Test.*`).

## Slice 3b: the public-name manifest and the facade (`3f75fba32`)

Files (20):
- Lean sources: `src/OCaml5/Lcnf/Naming.lean`, `src/OCaml5/Lcnf/Public.lean` (new),
  `src/OCaml5/Lcnf/Export.lean`, `src/OCaml5/Lcnf/Gen.lean`, `src/OCaml5/Ml/Syntax.lean`,
  `src/OCaml5/Ml/Render.lean`, `src/OCaml5/Ml/Check.lean`, `src/OCaml5.lean`;
- the recipe and the facade's library: `ocaml/gen/roots.json`, `ocaml/gen/facade/dune` (new);
- checks and documents: `scripts/lib/lcnf_interfaces.py`, `scripts/check-public-facade.py` (new),
  `Makefile`, `docs/GENERATED.md`, `ocaml/README.md`;
- generated: `src/OCaml5/Ml/Fold.lean`, `ocaml/gen/public-names.tsv` (new),
  `ocaml/gen/facade/effect4.ml` and `.mli` (new), the header of `ocaml/gen/api_gen.ml`.

What landed:
- `OCaml5.Lcnf.publicName (kind) (source)` and `publicNames` (`src/OCaml5/Lcnf/Naming.lean`). The
  rule:
  - the namespace components become modules;
  - a type is `t` in its own module;
  - a constructor is capitalised at its owner (`ownedCtor`);
  - a field keeps its owner's spelling (`fieldName`);
  - a value is spelled by `snake`. A reserved word takes `_`, `snake`'s one rule. A private, hygienic,
  numeric or compiler-made name (`_redArg`, `_at_`, `_lam_0`) is refused, never mangled.
  `publicNames` refuses two declarations with one path by both names, in the order listed.
- `Decl.moduleAliasD` in `src/OCaml5/Ml/Syntax.lean` (`module M = P`), with its render and check.
  The fold `src/OCaml5/Ml/Fold.lean` is regenerated by the derived family. The renderer now moves a
  module inside a module once per level; at the base a nested plain module moved twice. No earlier
  output nests a plain module, so no other generated file changed.
- `src/OCaml5/Lcnf/Public.lean` (new): the manifest rows, their text and reader, the append-only
  check `breaches`, the member spelling check `spellingMismatches`, and `facadeModule`.
- `src/OCaml5/Lcnf/Gen.lean`: `--facade`, `--public-manifest`, `--public-version`. The run that
  holds the public roots builds the manifest and the facade after every other check. It refuses
  an append-only breach before anything is written. `recipeArgvs` checks the public consumer's
  `facade_resolves` with the public paths as client names (`Export.ExportPlan.unresolvedAt`).
- `ocaml/gen/roots.json`: `facade` = module `Effect4`, out `ocaml/gen/facade/effect4.ml`,
  manifest `ocaml/gen/public-names.tsv`, version 0.
- Generated and committed: `ocaml/gen/public-names.tsv`, `ocaml/gen/facade/effect4.ml` (313
  lines) and its inferred `effect4.mli` (690 lines). The manifest has 377 lines: 93 values, 42
  program types, 9 sealed packages, 199 constructors and 31 fields. The `api_gen.ml` header line gains the three options.
- `ocaml/gen/facade/dune`: the library `effect4` (`public_name effect4_gen.effect4`,
  `-open Effect4_gen`).
- `scripts/lib/lcnf_interfaces.py`: the staged facade compiles against the staged artifacts, and
  its interface is inferred as theirs are, before any output is published.
- `scripts/check-public-facade.py` (new), run by `make check-ocaml`.

R6.2's six frozen paths are rows of the manifest: `Effect4.Program.Eff.t`,
`Effect4.Program.Eff.Succeed`, `Effect4.Program.Authoring.loop_with`,
`Effect4.Run.Tree.of_program`, `Effect4.Store.Val.t`, `Effect4.Tool.Native.Session.t`.

The facade's shape: a program type's module is an alias of its owner's module
(`module Eff = Eff_types.Eff`), so its constructors, fields and type equalities come with it. A
sealed package's `t` aliases the implementation's abstract type (`type 'a t = 'a Api_gen.checked`).
A value aliases the implementation's value (`let of_program = Api_gen.run_tree_of_program`). The
public types are the 42 types at the program types' owner and the 9 sealed packages.

The outside project (`scripts/check-public-facade.py`): `dune build @install` in `ocaml/`, then a
project in a temporary directory outside the repository, built with `OCAMLPATH` at
`ocaml/_build/install/default/lib`.
- Positive: it builds `Effect4.Program.Eff.Succeed (Effect4.Program.Term.Lit
  (Effect4.Program.Lit.Nat 42))`. It uses the facade's types as `Eff_types`' and `Api_gen`'s
  types, and runs the program through `Effect4.Run.Tree.settle`. It prints
  `settled after 0 steps; a nat is number`.
- Red, each refused by OCaml with the error it names:
  - `Effect4.Machine.Dispatcher.insert`, a coverage root: `Unbound module`;
  - `Effect4_gen.Api_gen.dispatcher_insert`, the same root through `Api_gen`: `Unbound value`;
  - `Effect4.Program.err_of`, a linkage root: `Unbound value`;
  - a `Built` literal through a client alias of `Effect4.Api.Built.t`;
  - `{ p with table = [] }` on `Effect4.Program.Prepared.t`;
  - a `Checked` literal;
  - `{ s with memo = [] }` on `Effect4.Tool.Native.Session.t`;
  - `[]` at `Effect4.Program.Check.Memo.t`.

The red controls of the naming and the manifest, each a fixture:
- `aB` and `a_b`: `publicNames` refuses both by name (`Naming.lean`), and so does `recipeArgvs`
  on a recipe with both public (`Gen.lean`).
- `breaches` (`Public.lean`) refuses a moved path, a dropped path, a changed arity and a version
  that goes back. It admits an appended row and a larger version.
- `facadeModule`: a value in a module that aliases an owner, and a row outside the facade's
  namespace, are refused. `spellingMismatches`: a member whose public name is not its owner's
  spelling is refused.

Reproduced through the driver, each against the committed manifest:
- `Effect4.Run.Tree.ofProgram` moved from `public` to `linkage` at version 0: exit 1, "the value
  Effect4.Run.Tree.ofProgram drops its public path Effect4.Run.Tree.of_program", nothing written.
- The same move at version 1: admitted, 92 values, the manifest's header `# version 1`.
- `Effect4.Run.Tree.aB` and `Effect4.Run.Tree.a_b` public: exit 1, both named, nothing written.
- `Effect4.Run.Tree.ofProgram` both public and coverage: exit 1, "is in two classes", nothing
  written.

Commands and results for 3b:

| Command | Result |
| --- | --- |
| `python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only derived` | `PASS generate`; only `src/OCaml5/Ml/Fold.lean` changed (17 lines) |
| `python3 /private/tmp/seams-lean-one.py lake build OCaml5 lcnfgen Conform.Effect4.LcnfMl Conform.Effect4.Normalization Test.Audit.ClockLowering Test.Audit.ConstructorOwners Test.Audit.LetReturn Test.Audit.LcnfMappedRecursion Test.Store.GallinaHeadPrinter` | 245 jobs, success |
| `python3 /private/tmp/seams-lean-one.py make batteries-touched BASE=4a81cc034` | `no battery reached` |
| `python3 /private/tmp/seams-lean-one.py make gen-lcnf` | `public face: 93 values, 42 program types, 9 sealed packages, 199 constructors, 31 fields; manifest version 0, 374 committed rows unchanged; Ml.checkModule: PASS` |
| `python3 scripts/check-public-facade.py` | `PASS: an outside project builds against effect4_gen.effect4 and runs; 8 red clients are refused by OCaml` |
| `python3 /private/tmp/seams-lean-one.py make check-ocaml` (before the member spelling check) | exit 0, `PASS ocaml: recorded 681f5ecec85a`, 6:55 |
| final `python3 /private/tmp/seams-lean-one.py make gen-lcnf` | exit 0, 2:33; the same public face; no generated file changed |
| final `python3 /private/tmp/seams-lean-one.py make check-ocaml` | exit 0: `PASS native`, `PASS compiler` and `PASS ocaml: shared result 681f5ecec85a`. The lane's inputs equal those of the 6:55 run above, so the gate reused its result. |
| `python3 scripts/check-public-facade.py`, `python3 scripts/check-export-classes.py`, on the final outputs | both `PASS` |

The 3a run of `batteries-touched` built 1,703 jobs. Its `.ilean` files were older than the
sources: the base audit had put the base sources back for a moment. The tool then reads edits by
name. With fresh `.ilean` files the touched set is empty.

Axiom output for 3b (`#axiom_audit`, through `lake env lean`), with the base beside it:

| Modules | Now | Base |
| --- | --- | --- |
| `OCaml5.Ml.Syntax`, `OCaml5.Ml.Fold` | 1,489 declarations within `[propext, Quot.sound]` | 1,478 |
| `OCaml5.Ml.Render`, `OCaml5.Ml.Check` | 30 of 212 reach `Classical.choice` | 30 of 212 |
| `OCaml5.Lcnf.Naming` | 25 of 185 | 20 of 52 |
| `OCaml5.Lcnf.Public` | 7 of 205 | new |
| `OCaml5.Lcnf.Export`, `OCaml5.Lcnf.Gen`, `OCaml5.Tools.LcnfGen` | 34 of 376 | 20 of 124 (no `Export`) |

Every path to `Classical.choice` enters through a toolchain constant: `String.startsWith`,
`String.Slice.toString`, `String.instLT`, `Lean.Name.toString`, `Lean.Json`,
`System.FilePath.fileStem`, and `Lean.getStructureFields` through `Classical.ofNonempty`. The
new ones in `Naming` are `publicComponents`, `publicName`, `publicNames`, `NameRefusal.message`
and the private control `pathOf`. `Public.breaches`, `Public.facadeModule` and the plan functions
of `Export` reach none.

## What moved on the wire

No codec, wire shape or digest moved. The recipe format moved from `effect4-lcnf-roots-v2` to
`effect4-lcnf-roots-v3`, with no reader for v2: the generator refuses a v2 recipe by its format.

## Found at the base

- `Test.Run.LiveContract` (imported by `Test/All.lean`) fails to elaborate at `4a81cc034`:
  `Effect4.Live.WaitView.registration` does not exist (`src/Effect4/Run/View.lean`). It imports no
  `OCaml5` module, and this branch changes no `src/Effect4` or `Test` file.
- Codex's R6.1 and R6.2 place their laws under "R12". The system map's R12 is "frontiers name what
  they await". The requirement for faces is R8, "runs and faces as named connections".

## Placement

No theorem landed, so no claim is placed. `facade_resolves` and `public_excludes_coverage` are
finite checks of the plan (`Export.ExportPlan.facadeResolves`, `publicExcludesCoverage`), and a
`CheckedPlan` carries their `= true` facts. The append-only check is a finite check of two
manifests (`Public.breaches`). R6.2 says passive name-table checks need local receipts only.
- Concept: `translation-simulation`, the generated interface's scope.
- Requirement: R8, faces as named connections.
- Not established: no theorem about the LCNF lowering, no equal behaviour of a facade value and
  its Lean definition, no hash or digest property. The checks hold for this recipe and these manifests.
- Unlocks: C5 starts from typed classes; F1 starts from fixed public paths; E1 can publish after
  the owner names the packages.

## What is open

1. Public types beyond the program types and the sealed packages. The facade's values name
   `Api_gen` types (`sig_app`, `sketch`, `type_refusal`, `tree`, `shape_doc`, `inspection`,
   `budget`, …) that have no public path yet; a client names them through `Effect4_gen.Api_gen`.
   F1 gives them paths, and the manifest then holds them append-only.
2. The lanes' roots are `linkage` in step 1, since each lane is its own unit. C5 makes them
   `coverage` with the lane as consumer when it writes one facade per consumer (R6.1).
3. `Api_gen`'s 17 linkage roots stay visible to an installed client through `Api_gen`. C5's
   scoped emission decides whether the test-only ones move to a test scope.
4. `publicName` takes a kind (`publicName (kind) (source)`); the brief's signature has none. A
   name alone does not say whether it names a type, a constructor or a value.
5. The reserved-word rule is `snake`'s: OCaml's keywords and `exit` take `_`
   (`Effect4.Program.Authoring.exit_`, `Effect4.Live.open_`, `Effect4.Program.Check.HitRule.or_`).
   The estate plan's §2.4 sketch writes `val exit`. Changing it is a version bump.
6. The append-only check holds paths, kinds, abstractness and a type's arity. A value's arity,
   labels and type sharing are held only by the committed `effect4.mli`, in review.
7. The facade's findlib name `effect4_gen.effect4` is in its dune file. R6.2 asks for package
   names once in the recipe; this waits for E1 (seat 2) and the owner's decision 3.
8. A public value in a program type's module (a future `Effect4.Program.Eff.size`) is refused by
   `facadeModule`: it needs an `include` form, which no output needs yet.
9. `Test.Run.LiveContract` fails at the base ("Found at the base"); `lake build Test` fails there.

## Proposed decisions row (the coordinator records it)

R6.1 step 1 and R6.2's naming slice (seat 3, wave 1). `ocaml/gen/roots.json` is format v3: each
root of each artifact has one export class (public, linkage, internal, coverage).
`OCaml5.Lcnf.Export` refuses a contradiction. The public face is the generated manifest
`ocaml/gen/public-names.tsv`, append-only at one version, and the facade library
`effect4_gen.effect4`, made from it. `Api_gen` keeps its names. The manifest's version is 0 until
the first release, and a larger version declares a break.

## Scratch outputs

This seat's scratch files sat in the session scratchpad; each was deleted after the last run.
They were this seat's own logs in `logs/`, and `census/`, `reorder/`, `redrun/`, `audit/`, `draft/`. The
worktree's `ocaml/_build` was deleted too (331 MB); a build recreates it.
