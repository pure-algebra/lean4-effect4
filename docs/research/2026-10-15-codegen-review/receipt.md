# 2026-10-15 seat codegen receipt: the codegen refactor, CR-0 to CR-12

Status: receipt (history, not authority). Branch `claude/codegen`, worktree
`/Users/pooks/Dev/lean4-effect4-codegen`, base `edae4e2b5`. The seat appends one section per
slice as the slice lands.

**The one thing to know before merging:** the TypeScript module that ships is not the typed
print everywhere. CR-1 found a well-typed program that the typed print refuses: the keyed lane's
`timeout/eager` client (`typed:term slot depth`, at an `iterate`). So the shipped module prints
each piece by the typed print, and by the fold where the typed print refuses (`shippedPieces`).
No verdict moves in any lane. The refusal is a defect of the eliminator-site printer, proposed
below as P-CR1-3.

## Baseline at the base `edae4e2b5`

Each gate ran once through the shared slot before the first change. The logs are in the seat's
scratchpad (`gates/base/`).

| Gate | Result at the base | Time |
| --- | --- | ---: |
| `lake build Effect4 Effect4.Laws Tools Test` | **fails** at `Test.Program.ModuleDefinitions` only: three guards call `DefDecl.readable []`, a stale call since `582aab12d` changed its first argument to a `TypeEnv`; 329 modules built, 2 restored | 333 s |
| `make check-docs` | **fails** on one stale reference: `docs/core/decisions.md` row 362 names `tools/view/make_videos.py`, which is untracked in the main tree | 37 s |
| `make check-language` | passes | 7 s |
| `make check-ts-reader` | passes: 781 tests | 8 s |
| `make check-tsdiag` | passes: 408 programs, no program this checker types is refused | 2 s |
| `make check-ingest-smoke` | passes: 408 comparisons on each parser | 1 s |
| `make check-target` | passes: 104 rows conform; 742 pairs, 708 agree, 6 cut, 28 incomplete; rows 67 queried, 42 agree, 3 mismatch, 22 refused | 8 s |
| `make check-truth` | passes: 81 programs agree, 12 signed divergences | 75 s |
| `make check-corpus` | passes | 117 s |
| `make check-host-protocol` | passes | 95 s |
| `make check-schema-codec` | passes: 49 comparisons | 3 s |
| `make check-schema-ts` | passes | 6 s |
| `make check-gen` | passes: no drift | 100 s |

The times include the wait for the slot, so they bound a gate's own time from above.

## CR-0: the import cut

### Base and head

Base `edae4e2b5`, head `3fcd80e94`.

### The one module that stays wide

CR-0 cuts the codegen out of the program interface's import closure, but one new module stays
wide. The refusal alphabets of the printer and the reader moved to `Effect4.Codegen.Refusal`,
which `Effect4.Api` imports, because the generated `src/Effect4/Api/RefusalsDerived.lean` reads
them through `Effect4.Api`. Its imports come from `tools/Effect4Gen/manifest.json`, which this
seat may not edit. That module's edit rebuilds 454 modules; every other core codegen module
rebuilds 16 to 91.

### What moved, and why each move serves the cut

The landing plan named three edges (`landing.md` §2.2). Reading the uses found four more, and
the first full build found a fifth.

| Edge | What the tree needed | The form landed |
| --- | --- | --- |
| `Effect4.Api` imports eight codegen modules | the face's codegen half | `src/Effect4/Api/Codegen.lean`, in the namespace `Effect4.Api`: `print`, `read`, `readAt`, `readable`, `roundTrip`, `imageCertificate`, `printDecl`, `emitModule`, `printModule`, `readModule`, `readFile`, `checkSourceBindings`, `admitModule`, `Typed.print`, `Typed.emit`, `TypedLayer.print`, `Built.print`, the Schema syntax and the exports `Target`, `Artefact` and `render`. The root `Effect4` and the entry module `Effect4.Emit` import it |
| the generated `Api/RefusalsDerived.lean` reads `PrintRefusal`, `ClassRefusal` and `ReadRefusal` through `Effect4.Api` | the three alphabets in scope of the module's fixed imports, which `tools/Effect4Gen/manifest.json` writes | `src/Effect4/Codegen/Refusal.lean`, a `module` file that imports nothing (decisions row 200); `Effect4.Api`, `PrintLeaf` and `Read` import it |
| `Laws.Program.Typed.Admission` reads `Eff.block?` from `Codegen.Print` | a program function, beside `Eff.defsOf` | `Eff.block?` in `src/Effect4/Program/Definitions.lean` |
| `Laws.Program.Typed.ListFold` imports `Laws.Codegen.ReadLeaf` | the plan read it as general lemmas; the claim `fold-typed-atomic-update` holds the leaf's printed equations in its statement (`ListFoldRules.readPrint`, `readExact`) | the codegen-free laws leave: `src/Effect4/Laws/Program/Typed/FoldEval.lean` (`evalTerm_weaken`, `foldlM_refuses`, `refModify_typed_step`) and `src/Effect4/Laws/Program/Typed/HandleIdentity.lean` (the claim `handle-identity-laws`). `ListFold` keeps its claim and its import; its consumers import the two new modules |
| `Laws.Step.Waiting` imports `Laws.Codegen.Mask` | the mask's derived form and its typing, read through the claim `mask-printed-form-profile`, whose statement holds the form's round trip | `maskForm`, `maskForm_typed`, `restore_typed` and `restore_untyped` in `src/Effect4/Laws/Program/Typed/Mask.lean`; `Waiting` reads `maskForm_typed` |
| `Laws.Step.Reading` reads `repr_inj` from `ReadLeaf` | a decimal law | `Effect4.Data.NatDecimal.repr_inj`, in `src/Effect4/Laws/Data/NatDecimal.lean` |
| the face imported `Api.Author` for `Built.print`, and `Author`'s closure makes `daemon` a keyword, which broke `Test.Program.AuthoringContract`'s structure literal | `Built.typed`, beside `Built` | `Built.typed` in `src/Effect4/Api/Built.lean`; the face imports `Api.Built` |

Two consumers now read a field's theorem in place of a claim's top node.
`step_keeps_cell` (`src/Effect4/Laws/Step/Store.lean`) reads `refModify_typed_step`, the `step`
field of `fold_typed_atomic_update`. The waiting wrapper's typing reads `maskForm_typed`, the
`typed` field of `mask_printed_form_profile`. No statement, pointer or placement changed. The
regenerated report (`generated/semantics.md`) shows the effect in R4's plan. Its graph no longer
passes through `mask_printed_form_profile`, `saved_mask_restoration` and `read_print`. They came
into it only through the mask claim's bundled statement. Every status is unchanged.

`ReadLeaf`'s copies went: the review's three (`bind_eq_ok`, `map_eq_ok`, `utf8_digitChar`) and
four decimal wrappers of the same kind (`decodeBytes_append`, `digitOfByte_digit`,
`decodeBytes_toDigitsCore`, `decodeBytes_repr`). The eight law modules that read the inversion
lemmas open `Effect4.Laws.Auto (bind_eq_ok map_eq_ok)`.

### Changed files

98 files: 94 modified and 4 new.

- The four new modules above, and the modules they left: `src/Effect4/Api.lean`,
  `src/Effect4/Api/Author.lean`, `src/Effect4/Api/Built.lean`, `src/Effect4/Codegen/Print.lean`,
  `src/Effect4/Codegen/PrintLeaf.lean`, `src/Effect4/Codegen/Read.lean`,
  `src/Effect4/Program/Definitions.lean`, `src/Effect4/Laws/Program/Typed/ListFold.lean`,
  `src/Effect4/Laws/Program/Typed/Mask.lean`, `src/Effect4/Laws/Codegen/Mask.lean`,
  `src/Effect4/Laws/Codegen/ReadLeaf.lean`, `src/Effect4/Laws/Data/NatDecimal.lean`.
- The consumers: `Laws.Step`, `Laws.Step.Store`, `Laws.Step.Reading`, `Laws.Step.Waiting`,
  `Laws.Library.Queue.Steps`, `Laws.Api.Codegen`, `Laws.Codegen.Definitions`, and the eight
  modules of the inversion lemmas.
- The root import `src/Effect4.lean`: one line appended at the end of its import block
  (`import Effect4.Api.Codegen`, with its comment). `src/Effect4/Laws.lean`, `Test/All.lean` and
  `Test/Audit/AxiomGate.lean` are unchanged.
- The importers: 47 batteries name the face (`Effect4.Api.Codegen`, or `Effect4.Emit` in the
  acceptance programs, which import entry modules); `tools/Drivers/Corpus.lean`,
  `tools/Tools/Code/Module.lean`, `tools/TestSupport/ServiceIdentity.lean`; nine harness
  scripts.
- Two stale callers of `DefDecl.readable`, failing at the base since `582aab12d`:
  `Test/Program/ModuleDefinitions.lean` (three guards, `[]` to `{}`, the empty type
  environment) and `harness/channel-transforms/Produce.lean`.
- Regenerated: `src/Effect4/Api/RefusalsDerived.lean` (its carrier line names
  `Effect4.Codegen.Refusal`) and `generated/semantics.md` (the module of
  `handle-identity-laws`, and R4's plan).
- The documents: `docs/ARCHITECTURE.md` (the face's rows; the stale hand count of module-system
  files removed), `docs/core/api-surface.md`, `docs/core/semantics.md` (the path of
  `handle_identity_laws`).

### Commands and results

Every command ran through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. A time
includes the wait for the slot.

| Command | Result | Time |
| --- | --- | ---: |
| `lake build Effect4.Codegen.Refusal Effect4.Api Effect4.Api.Author Effect4.Api.Codegen Effect4.Emit Effect4.Api.RefusalsDerived Effect4.Program.Definitions` | passes, 183 jobs | 397 s |
| `lake build Effect4 Effect4.Laws Tools Test`, first run | fails at `Test.Program.AuthoringContract` only: `daemon` is a keyword through `Api.Author` | 1650 s |
| the same, after `Built.typed` moved | passes, 2235 jobs | 855 s |
| `python3 scripts/generate.py --only derived` | one line of `RefusalsDerived.lean` changes | 154 s |
| `#axiom_audit` over the 28 touched modules at the base, against the main tree's build | 8286 declarations within `[propext, Quot.sound]` | 149 s |
| `#axiom_audit` over the same 28 modules and the 4 new ones | 8276 declarations within `[propext, Quot.sound]` | 116 s |
| `make check-docs` | the base's one stale reference, no other | 1 s |
| `make check-language` | passes | 7 s |
| `make check-gen` | the two regenerated files differ from the base, as committed; nothing else | 96 s |
| `make check-ts-reader`, `check-tsdiag`, `check-ingest-smoke`, `check-target`, `check-truth`, `check-corpus`, `check-host-protocol`, `check-schema-codec`, `check-schema-ts` | each passes with the base's result lines; the host lane's lines differ only in a temporary folder's name | 4 s to 111 s |
| `lake env lean` on the eleven harness and application scripts | each elaborates | — |

The whole-tree gates of the second full build (`Test/All.lean`) report:

- the library-root gate: 276 API or utility modules and 622 Laws-only modules, every library
  source reachable;
- the axiom gate: 1358 modules and 126791 declarations, with its boundary of 22 modules and 49
  declarations;
- the goal gate: 25 planned goals, with 34 declarations on them.

### Axiom output

The two audits differ by 10 declarations, each named by a listing of the audited names in both
environments:

- the seven deleted copies;
- three auxiliaries of `Eff.block?` (`match_1`, `_sparseCasesOn_1` and its `else_eq`): in the
  module-system file `Program/Definitions.lean` its match is `Checker.checkModule`'s matcher;
- `repr_inj` changes its namespace to `Effect4.Data.NatDecimal`;
- the matchers of the three alphabets' `Repr` instances and four equation lemmas change their
  private names.

### The rebuild, measured

`probes/fanout.py` counts each module's importers in `src/` and `tools/`. Its walk of `Test/`
compares `root/./Test` with `root/Test`, so it counts no battery. The last column counts the
batteries too, by the same scan with that comparison repaired.

| Module | Rebuilt before | Rebuilt after | Law modules after | With the batteries, before and after |
| --- | ---: | ---: | ---: | --- |
| `Effect4.Codegen.Print` | 444 | 77 | 19 | 790, 282 |
| `Effect4.Codegen.Checked` | 417 | 48 | 5 | 756, 229 |
| `Effect4.Codegen.Types` | 458 | 91 | 24 | 810, 308 |
| `Effect4.Codegen.Read` | 439 | 72 | 18 | 783, 275 |
| `Effect4.Codegen.Schema` | 415 | 46 | 4 | 757, 230 |
| `Effect4.Codegen.Metadata` | 457 | 90 | 24 | 807, 299 |
| `Effect4.Codegen.PrintLeaf` | 450 | 83 | 20 | 798, 290 |
| `Effect4.Codegen.Templates` | 445 | 78 | 19 | 791, 283 |
| `Effect4.Codegen.Refusal` (new) | — | 454 | 366 | —, 802 |
| `Effect4.Laws.Codegen.ReadLeaf` | 64 | 15 | 14 | — |
| `Effect4.Laws.Codegen.Mask` | 15 | 2 | 1 | — |

Every core codegen module rebuilds under 100 modules except the refusal alphabet. The
alphabet holds three inductive types of plain data; CR-8 edits it once.

### Lines removed and added

819 lines removed and 1015 added, the four new modules' 737 lines among them. The moves are
neutral in lines; the added lines are the new modules' notes and the face's docstrings.

### Evidence

- Proved: the whole tree within `[propext, Quot.sound]` and its boundary (the axiom gate of
  `Test/All.lean`), and the touched modules (`#axiom_audit`).
- Tested: the nine behaviour gates above, against the base's result lines.
- The counts of rebuilt modules are a scan of import lines, not a build.

### Landed theorems and their placement

No new theorem. Each moved declaration keeps its name, statement and placement. The exception
is `repr_inj`, whose namespace is now `Effect4.Data.NatDecimal`. It is an untagged helper of the
binder law `Var.name_inj` and of `mint_depth_inj`.

### Open obligations

- `README.md`, the owner's, says that `Effect4.Api` holds `print`, `printDecl` and the Schema
  syntax. They are `Effect4.Api.Codegen`'s now, which the root `Effect4` imports.

### Proposed decisions rows (proposals only)

- **P-CR0-1.** After the lowering branch merges, the Refusals group of
  `tools/Effect4Gen/manifest.json` imports `Effect4.Api.Codegen` in place of `Effect4.Api`.
  `Effect4.Api` then drops `Effect4.Codegen.Refusal`, and the alphabet rebuilds what the codegen
  face rebuilds, not 454 modules.

## CR-3: `check-target` asks tsgo about the shipped spelling

### Base and head

Base `2985e6ed0`, head `be5cfb832`.

### Changed files

- `tools/Tools/TypeSpelling.lean` (new): `Tools.TypeSpelling.spelled`, the type printer
  `Codegen.Types.ofTy` rendered flat at the house style, as the module writer renders a type.
- `tools/Tools/TyVectors.lean`: each pair at that spelling; a pair whose type has no printed
  form is refused by its id.
- `tools/Tools/RowTypes.lean`: every selectable row's signature at that spelling, through
  `Except`; a type with no printed form refuses the table by name.
- `tools/target/assignability.ts`: the cut's reason names the shipped spelling. The comments of
  `oracle.ts`, `profile.ts` and `rows.ts`, and `tools/target/README.md`, follow.
- `generated/row-types.tsv` and `generated/assignability.tsv`, promoted.

### Commands and results

| Command | Result | Time |
| --- | --- | ---: |
| `lake build Tools.TypeSpelling Tools.TyVectors Tools.RowTypes` | passes | 5 s |
| `lake env lean -M4096 --run tools/Tools/RowTypes.lean generated/row-types.tsv` | only the header line moves: every row's spelling is the same under the shipped printer | — |
| `lake env lean -M4096 --run tools/Tools/TyVectors.lean`, diffed with the base's vectors | 14 of 742 pairs change their spelled columns, each at one of the probe's two types | — |
| `make gen-assignability` | 742 pairs: 708 agree, 10 cut, 24 incomplete, no defect; the red control is caught by 10 pairs | — |
| `make check-target` | passes: 104 rows conform; 742 pairs as above; rows 67 queried, 42 agree, 3 mismatch, 22 refused, as at the base | 15 s |

### Evidence

- Tested: four verdicts moved, each from `incomplete` to `cut`. Their two sides now print one text:
  `literalPair/0-1`, `literalPair/1-0`, `bound/2-3` and `bound/3-2`.
  `Ty.sub` relates the two types one way, and the printer, which normalizes first, spells both as
  one union of tuples. Each pair holds one of the two types that the review's probe found
  (`probes/type-spellings.log`). No verdict outside them moved.
- The order column stays `Ty.sub`, the raw order. The checker compares with `Ty.subN`, `sub`
  after `normalize`, under which these pairs relate both ways. This seat changes no column
  of the order.

### Axiom output

No declaration of `Effect4.*` or `Test.*` changed: the edits are in the tool root `Tools`.

### Lines removed and added

100 lines removed and 158 added, the new module's 31 among them, in 10 files.

### Open obligations

- The gate's marker does not depend on `tools/Tools/TypeSpelling.lean`: `$(CHK)/target` names
  `tools/Tools/RowTypes.lean` and `tools/Tools/TyVectors.lean` but not their imports, and
  `LEAN_INPUTS` reads `src` and `Test` only.

### Proposed decisions rows (proposals only)

- **P-CR3-1.** `$(CHK)/target` in the `Makefile` adds `tools/Tools/TypeSpelling.lean` to its
  prerequisites, so an edit of the shipped spelling re-runs the gate. The `Makefile` is the
  coordinator's while the lowering branch is open.

## CR-1: one emission route

### Base and head

Base `9a699340a`, head `bdf074d15`.

### What landed, step by step

| Step of the plan | The form landed |
| --- | --- |
| 1. `printEntry` prints through `printTyped` | one module printer over a printer of the program pieces (`printModuleWith`, `printEntryWith`, `PiecePrint`, `src/Effect4/Codegen/Print.lean`); the checked emission prints its pieces by `shippedPieces` (`src/Effect4/Codegen/PrintTyped.lean`): the typed print, and the fold where the typed print refuses; `printModule` and `printEntry` are the plain instances; `Api.printDecl` prints its body as the module does |
| 2. `typeArgsAt` reads the `annotate` table | `typeArgsAt s entries p` reads the focus off the table (`focusAtTable`, `Focus.joinArgs`); the old focus-based `typeArgsAt` is gone |
| 3. unchecked programs get the same writer | `uncheckedFile` (`src/Effect4/Codegen/Checked.lean`), and the one writer of every lane, `Tools.Code.programModule` (`tools/Tools/Code/Module.lean`) |
| 4. the truth modules' text in Lean | `harness/truth/Truth.lean` writes `module`, `moduleInferred`, `moduleSource`, `moduleRefusal` and `expr` (the main initializer, flat); `run-truth.ts` writes `module` as it is; the service clients are Lean syntax inside the module, so its imports cover them; the truth lane's host binds its row namespaces from its prelude (`hostImports`) |
| 5. the corpus's module texts in Lean | `tools/Drivers/Corpus.lean` writes `.lake/corpus/modules/<name>.ts` and the lane's two controls; `harness/tsdiag/run-tsdiag.mjs` reads them as they are |
| 6. `bindingsType` into the core | `hostBindings` (`src/Effect4/Codegen/RowServices.lean`), a structured type whose methods are the service methods' fields (`rowMethodField`); the keyed lane's scenario module is Lean's (`scenarioModule`), under the host's header of bindings |
| 7. `ts/eff/read.ts` reads a join's type arguments | a reading mode, `Joins`: `erase` reads the bare call where neither the operation nor its row carries type arguments, as `eraseRowJoin` does; `ts/eff/check.ts` reads with `erase` |
| 8. the erasure lifted to modules | one module reader over a reader of the pieces (`readModuleWith`, `PieceRead`, `src/Effect4/Codegen/Read.lean`); `readModuleTyped` reads each piece by `readTyped`; `admitModule`, `Api.readModule` and `Api.readFile` read so |

P2b's module (`harness/truth/P2b.lean`) comes from Lean too, with its imports from Lean data
(`fileOf`); `scripts/check-truth.py` writes it as it is.

### Two departures from the plan, each with its cause (row 390)

- **The fold where the typed print refuses.** The typed print refuses the keyed lane's
  `timeout/eager` client: the `iterate` at the address `[1, 1, 1, 0]` of its hoisted main
  program, with `internalAction "typed:term slot depth"` (`PrintEliminators.printArg`). There a
  term slot's checked environment is not the template's binder depth. Under the plain typed print
  the scenario's script had no host run: 86 scripts in 294 runs, against 87 in 297 at the base.
  Under `shippedPieces` the script runs as at the base. The probes are the seat's
  `cr1/probe/Eager*.lean`. The fallback serves the same users: every module that printed still
  prints, typed where the typed print succeeds.
- **The diagnostics lane checks the unchecked module.** Under the module that ships, with its
  declared type, `g309` moves from `typed-clean` to `typed-errors`, and the lane fails. The
  corpus lane registers the same TS2375 for `g309` in `harness/truth/corpus-known-differences.md`:
  tsgo infers `Fiber<unknown, unknown>` from a never value. So the diagnostics lane checks each
  program as `export const main = …` with no declared type, by the one writer. Whether it checks
  the module that ships is P-CR1-2.

### Deletes

- `joinedOutput`, `fixtureOutput` and `joinedFixtures` of `harness/truth/Truth.lean`;
- `importHeader` and the module assembly of `harness/truth/run-truth.ts`;
- `columnType` and `bindingsType` of `harness/truth/session/Keyed.lean`, and the keyed header's
  lists of `effect` and prelude names (`run-keyed.ts`);
- the diagnostics lane's module writer and the corpus's `expanded/` twins;
- P2b's header from `module-imports.ts` (`scripts/check-truth.py`).

`harness/truth/module-imports.ts` stays: no code reads it, and `TRUTH_SOURCES` in the `Makefile`
names it, so deleting it stops `make gen-truth` (P-CR1-1).

### Changed files

39 source files and 95 generated ones.

- The core: `src/Effect4/Codegen/{Print,Read,PrintTyped,Checked,Admit,RowServices}.lean` and
  `src/Effect4/Api/Codegen.lean`.
- The laws: `src/Effect4/Laws/Codegen/{Module,PrintTyped,Checked,Admit}.lean` and
  `src/Effect4/Laws/Api/{Codegen,ModuleReadable}.lean`; docstrings only in
  `src/Effect4/Laws/Codegen/{Classes,Definitions,RowServices,Services}.lean` and
  `src/Effect4/Laws/Program/Hoisting.lean`.
- The tools and lanes: `tools/Tools/Code/Module.lean`, `tools/Drivers/Corpus.lean`,
  `tools/target/{checker,corpus,oracle}.ts`, `harness/truth/{Truth,P2b}.lean`,
  `harness/truth/run-truth.ts`, `harness/truth/session/{Keyed.lean,run-keyed.ts}`,
  `harness/tsdiag/run-tsdiag.mjs`, `scripts/check-truth.py`, `ts/eff/{read,check}.ts` and
  `ts/eff/test/read.test.ts`.
- The documents: `docs/ARCHITECTURE.md`, `docs/GENERATED.md`, `docs/STATE.md`,
  `docs/core/semantics.md`, `docs/core/host-boundary.md`, and an amendment of
  `Test/contracts/faces.contract.md`.
- Regenerated: `harness/truth/corpus.json`, the 93 modules of `harness/truth/generated/`, and
  `generated/semantics.md`.
- No root import and no gate of `Test/Audit/AxiomGate.lean` changed.

### Commands and results

Every command ran through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`; a time includes
the wait for the slot. From this slice on, `make` runs with `BUN="bun --no-install"`. CR-0's and
CR-3's gates ran with the `Makefile`'s plain `bun`.

| Command | Result | Time |
| --- | --- | ---: |
| `lake build Effect4`, twice as the core changed, and a third time with the law modules | passes, 296 jobs | 108 s, 18 s, 147 s |
| `lake build` of the six touched law modules | passes, 388 jobs | 121 s |
| `lake build Effect4.Laws` | passes, 1102 jobs | 9 s to 52 s |
| `lake build` of the 57 batteries and tools that import a touched module | passes, 1327 jobs | 177 s |
| `lake env lean` on `Truth.lean`, `P2b.lean`, `session/Keyed.lean` | each elaborates | — |
| the truth manifest, diffed with the committed one before any host run | no field but the module fields moved; every module's declarations equal the base's flat block up to whitespace; `expr` moved for 15 programs, the 14 block programs that had none and `pDiamond`, whose main is hoisted | — |
| `make corpus`, diffed | `generated/corpus-index.tsv` unchanged | 85 s |
| `make gen-truth` | `result.json`, `result.md` and the tapes unchanged; 81 programs agree, 12 signed divergences | 186 s |
| `make check-truth` | passes, with the widening controls and P2b | 71 s |
| `make check-corpus` | passes: the base's line, 400 programs match the committed results | 114 s |
| `make check-tsdiag` | passes: the base's table, 136 typed-clean | 1 s |
| `make check-ts-reader` | passes: 416 matched, as at the base; 73 accepted without an oracle (71 at the base: the two `pJoinedModify` modules read under `erase`); 783 tests | 3 s |
| `make check-target` | passes: CR-3's line | 9 s |
| `make check-ingest-smoke` | passes: the base's line | 1 s |
| `make check-host-protocol` | passes: the base's lines, 87 scripts in 297 runs | 94 s |
| `make gen-semantics` | `generated/semantics.md` moves: the claim's docstring, and `printTyped_eq_print` rests on `focusAtTable_annotate` too; every status unchanged | 286 s |
| `make check-docs` | the base's one stale reference, no other | 0 s |
| `make check-language` | passes | 7 s |
| `bun --no-install test test/read.test.ts` in `ts/eff` | 132 pass | 1 s |

### Axiom output

`#axiom_audit` over the 18 touched modules of `Effect4`: 4251 declarations within
`[propext, Quot.sound]`, none modulo planned goals.

### Landed theorems and their placement

- `focusAtTable_annotate` (`src/Effect4/Laws/Codegen/PrintTyped.lean`): concept `exact-codecs`, a
  step of the claim `typed-print-connector` (R8). Its consumer is `printTyped_eq_print`, which keeps
  its statement. Reach: every program and every address. It says nothing of the cost.
- `readModuleWith_printModuleWith` and `readModuleWith_printModuleWith_defs`
  (`src/Effect4/Laws/Codegen/Module.lean`): steps of `module-defs-round-trip` (R8). Consumers:
  the plain instances, `readModule_printModule_defs` the claim's pointer, and the laws below.
- `PiecesLawful`, `shippedPieces_lawful`, `readModuleWith_printModuleWith_readable`,
  `readModuleWith_printModuleWith_defs_readable` (`src/Effect4/Laws/Api/ModuleReadable.lean`):
  steps of `module-defs-round-trip`, through `readTyped_printTyped` (`typed-print-read`).
  Consumer: `ModuleEmission.readDecls`.
- `printModuleWith_readable` and `shippedPieces_prints`: steps of `emitModule_complete`, which
  keeps its statement.
- No requirement, claim or planned goal is added. What changes in the contract's statements is
  in its amendment of 2026-10-15.

### Lines removed and added

529 lines removed and 1101 added in the 39 source files. The 95 regenerated files add 25295 lines
and remove 2730. A module laid out at Effect's width is longer, and the manifest holds two views
of it.

### Evidence

- Proved: the laws above, under `[propext, Quot.sound]` (`#axiom_audit`).
- Tested: the nine behaviour gates, against the base's result lines; no program's verdict moved.
- Reproduced: the truth lane's committed files, the corpus index and the semantics report.

### Open obligations

- The eliminator-site printer refuses `timeout/eager` at a term slot (P-CR1-3).
- `Ty.maskRestoreTarget` is no `preludeNames` member. A module whose annotation names
  `MaskRestore` imports nothing for it. No program of a lane prints it today.
- The keyed lane's plain fixtures keep their `build` template: the program is an expression under
  the host's bindings, and `CASES_SHA256` pins their recordings.
- The TypeScript reader reads no type that the typed print writes at an eliminator's site.

### Proposed decisions rows (proposals only)

- **P-CR1-1.** `TRUTH_SOURCES` in the `Makefile` drops `harness/truth/module-imports.ts`, and the
  file is deleted. No code reads it.
- **P-CR1-2.** The owner rules what the diagnostics lane checks. (a) The module that ships, with
  a register of known differences, as the corpus lane keeps one. (b) The unchecked module, as
  now. Recommend (a): the lane would then check what an agent ships.
- **P-CR1-3.** Register the slot-depth refusal as a counterexample of the typed print, and repair
  the site printer. CR-7 found the cause. An `iterate`'s body prints under the cursor's binder,
  at depth `n + 1`. The checker types it without the cursor, at length `n`. The options and the
  recommendation are in `cr7-note.md` (§4). The fallback in `shippedPieces` then goes.

## CR-7: stopped at a decision boundary

### Base and head

Base `1a72faa90`; the design note's commit is the head. No Lean source changed.

### Why it stopped

Step 4 deletes the row-only printer. The site printer would then print every program, and it
refuses a well-typed one: `timeout/eager`, at a term slot in an `iterate`'s body. The body prints
at depth `n + 1`, under the cursor's binder, and the checker types it at length `n`. So the
deletion would cost such programs their typed print. It would also change the statement of
`printTyped_eq_print` (`typed-print-connector`), which is CR-7's stop rule. The repair of the
site printer is a design choice with three options, and the note recommends one
(`docs/research/2026-10-15-codegen-review/cr7-note.md`, §4).

Steps 1 and 2 do not depend on the repair, but their order does. Fused before the repair, the law
covers two printers; after it, one. The note measures the module's parts. A fusion over both
printers saves about 40%, not the review's 2,000 lines; the row-only erasure alone is 3,100 of the
8,236 lines.

### Changed files

- `docs/research/2026-10-15-codegen-review/cr7-note.md` (new).

### Commands and results

| Command | Result |
| --- | --- |
| the locating probes, `lake env lean` on the seat's `cr1/probe/Eager2.lean` to `Eager4.lean` | the deepest refusing address is the `iterate` at `[1, 1, 1, 0]`; its term slots agree with the template's depths, and its body's checked length is one less than its print depth |
| `python3 scripts/check-language.py --strict` on the note | passes |

### Axiom output

None: no declaration changed.

### Open obligations

- CR-7's five steps, in the note's order, after the owner or the coordinator rules P-CR1-3.

### Proposed decisions rows (proposals only)

- **P-CR7-1.** Rule P-CR1-3 by the note's option (a): the site printer pads a slot's environment
  with the binders that the template adds. Then CR-7 runs as the note orders it. The row-only
  printer and its erasure go, and the connector moves to the site printer with its statement.
  Then the site erasure's casework fuses.

## CR-9: superseded code, and the claim's pointer

### Base and head

Base `b857068f3`; the slice's commit is the head.

### What landed, step by step

1. **`Artefact` went, by deletion.** `Codegen.Target` loses `Artefact`, `Artefact.of`,
   `Artefact.target`, `target_of` and `Artefact.render`. The program interface's codegen face
   loses its export of `Target`, `Artefact` and `render`.
   - The live users were the face's export, one battery line (`Test/Api/ApiContract.lean`) and
     the axiom gate's exemption. The build's reference files (`.ilean`) show it, less the stale
     files of modules deleted earlier (`Effect4.Codegen.App`, `Rule`, `Package`, `Emit`).
   - The other option was to make `moduleText` the body of `render`. It would move the tool's
     layout printer into the core, under the axiom gate (`tools/Tools/Code/`, about 1,200 lines
     with its laws). The seat took the deletion.
   - The target alphabet `Target` stays: it is the tree anchor of the dictionary's word
     **target**. The JSON text stays: `Effect4.Laws.Author.Explain` and a Schema battery read it.
2. **The foreign styles' target syntax moved to the ingest tool.** `src/Effect4/Codegen/Styles.lean` is
   now `tools/Drivers/StyleSyntax.lean`, beside its reader `Drivers.Styles`.
   - Its declarations keep their namespace, `Effect4.Codegen.Styles`. The driver beside it kept
     `Tools.Styles` when it moved, so the tree's precedent is the same.
   - Its readers are the driver and one battery (`Test/Codegen/FormsContract.lean`). The battery
     imports the tool module now, as other batteries import tool modules.
   - The move changes the header docstring alone (`git diff -M`, reading).
   - Its declarations leave the axiom gate's audit, since `Drivers.*` is no `Effect4.*` module.
     They stay within the ceiling (the axiom output below).
3. **The three lemma copies** went in CR-0 (`3fcd80e94`).
4. **The nine `#print axioms` lines and the two restatements went.** The lines were in
   `Test/Audit/LetReturn.lean`, `Test/Audit/ProofGraph.lean`, `Test/Audit/ProofGraphSearch.lean`
   and `Test/Counterexamples/Machine/Runtime/HostReservedDefect.lean`. The restatements were the
   two examples of `Std.lt_irrefl` and `Std.lt_trans` in `Test/Data/RowContract.lean`.
5. **The claim `module-defs-round-trip` points at `Api.printModule_roundTrip`** (CG-14, the
   review's P11 (a)). Its title already named that theorem. Its status stays proved.

The documents follow the code:
- `README.md` named `Api.render (.ts e.module)` as the way to emit TypeScript. It now names the
  emission's file and `moduleText`.
- `README.md` also named `print` and `printDecl` as `Effect4.Api`'s. CR-0 moved them to
  `Effect4.Api.Codegen`, so the README now names both modules.
- The dictionary's row **artifact** had `Artefact` as its tree anchor. It now means a produced
  file, anchored at `docs/GENERATED.md`.
- `docs/ARCHITECTURE.md` and the module docstrings no longer name a render crossing in the face.
- The contract cites the moved module at its new path, and at the old one by revision
  (`Test/contracts/faces.contract.md`). Its row 6 cites a moved module the same way.

### Changed files

- Core: `src/Effect4/Codegen/Target.lean`, `src/Effect4/Api/Codegen.lean`,
  `src/Effect4/Api.lean` (docstring), `src/Effect4.lean` (the comment at Target's import, and the
  import of `Styles` removed at its anchor), `src/Effect4/Laws/Codegen/Module.lean` (docstrings).
- Moved: `src/Effect4/Codegen/Styles.lean` to `tools/Drivers/StyleSyntax.lean`.
- Tools: `tools/Drivers/Styles.lean` (its import), `tools/ProofGraph/Registry.lean` (the
  pointer).
- Codegen batteries: `Test/Api/ApiContract.lean`, `Test/Codegen/FormsContract.lean`, and
  `Test/Codegen/SchemaGenerationContract.lean`, which now imports the JSON text it reads.
- Docstrings of batteries: `Test/Codegen/ServicesPrint.lean`, `Test/Codegen/DefinitionsPrint.lean`.
- The gate: `Test/Audit/AxiomGate.lean`, its exemption removed at its anchor.
- The battery lines: `Test/Audit/LetReturn.lean`, `Test/Audit/ProofGraph.lean`,
  `Test/Audit/ProofGraphSearch.lean`, `Test/Data/RowContract.lean` and
  `Test/Counterexamples/Machine/Runtime/HostReservedDefect.lean`.
- Documents: `README.md`, `docs/ARCHITECTURE.md`, `docs/core/controlled-english.md`,
  `docs/core/semantics.md`, `Test/contracts/faces.contract.md`.
- Regenerated: `generated/semantics.md`.

### Commands and results

Every `lake` and `make` command ran through the shared slot. The logs are in the seat's
scratchpad (`cr9/`, `gates/cr9/`).

| Command | Result |
| --- | --- |
| the narrow build: the edited modules, the direct importers of `Codegen.Target` and `Api.Codegen`, and the edited batteries (`cr9/build1.sh`) | passes: 1,355 jobs, 271 compiled, 381 s |
| `make gen-semantics` | passes: 1,670 jobs, 524 s. The report moves the claim's row and its entry alone: the pointer, its docstring, module and statement. The status stays proved |
| `make check-ingest-smoke` | passes: 408 exact JSON and wire comparisons on each parser; the corpus index is byte-identical |
| `make check-docs` | fails on the base's one stale reference: decisions row 494 names `tools/view/make_videos.py`, untracked in the main tree |
| `make check-language` | passes |
| `python3 scripts/check-language.py --show` on the five edited documents, against their head copies | no finding added; two removed (`README.md` and `docs/ARCHITECTURE.md`) |
| `lake env lean --run tools/Drivers/Corpus.lean --foreign <dir> 400 4`, the nightly lane's step | writes the foreign corpus through the moved module: 22,419 files, 21 isolated styles, 11,520 products |
| `bun --no-install ts/eff/ingest/check-coverage.ts <dir>` | fails: `missing eff coverage: defs, invoke` |
| `bun --no-install ts/eff/ingest/cli.ts gate --printed .lake/corpus --foreign <dir>` | the printed half passes; the foreign half fails its file-count pin, 22,398 |
| the pointer probe, `lake env lean` on `cr9/PointerProbe.lean` (the review's probe's imports) | the roots are 328. The load-bearing theorems go from 10,204 to 10,320: 117 gained, 1 lost |

The two nightly failures are the lane's own, not the move's (reading). The pin of 22,398 dates
from 2026-10-06. `3bada1241` (2026-10-11) added a provider probe under each of the 21 styles, so
the corpus holds 22,419. No generated program holds a definition block, so the foreign corpus
covers neither `defs` nor `invoke`, which slices HO-1 and HO-2 added on 2026-10-10. The main
tree's marker of `check-ingest` is from 2026-10-07. `check-ingest` is the nightly lane, not a
gate a landing owes.

The pointer probe, by module:

| Module | Theorems | Load-bearing before | Load-bearing now |
| --- | ---: | ---: | ---: |
| `Effect4.Laws.Codegen.Definitions` | 65 | 0 | 65 |
| `Effect4.Laws.Api.ModuleReadable` | 15 | 0 | 8 |

The other gains are 17 in `Effect4.Laws.Codegen.ReadLeaf`, 10 in `Effect4.Program.Native` and 17
across eleven more modules, two of them Lean's own (`Init.Data.List.Find`, `Init.Data.Nat.Basic`). The theorem lost is the old pointer, `readModule_printModule_defs`: the
face theorem reaches the module law at the typed pair, not its plain instance. It keeps its
placement at R8 (`@[semantics "exact-codecs" (requirement := R8)]`), so it stays a node of R8.
The review counted 78 theorems in the two modules: 65 and 13. `ModuleReadable` holds 15 theorems
since CR-1, and 8 of them carry load.

### Axiom output

`#axiom_audit` (`cr9/AuditCR9.lean`):
- `Effect4.Codegen.Target`: 13 of 93 declarations reach `Classical.choice`. Each is a JSON text
  renderer or its auxiliary: `JsonText.escape`, `render`, `renderList`, `renderEntries` and
  `renderJson`. The gate exempts each by exact name. `Artefact.render` left that list.
- The fourteen other modules this slice edits: 982 declarations within `[propext, Quot.sound]`,
  2 of them modulo planned goals. The one planned goal is the fixture `leaf` of
  `Test/Audit/ProofGraph.lean`, which the battery declares to test the goal commands.
- `Drivers.StyleSyntax`: 389 declarations within `[propext, Quot.sound]`.

### Lines removed and added

Without the regenerated report, 152 lines removed and 81 added in 24 files. The report removes 71
lines and adds 18.

### Evidence

- Reproduced: the semantics report and the printed corpus's index.
- Tested: the narrow build, `check-ingest-smoke`, and the foreign corpus written through the moved
  module.
- Proved: no new statement. The claim's pointer is a theorem the tree held.
- Reading: the move changes one docstring; the two nightly failures predate the slice.

### Open obligations

- `Effect4.Codegen.EraseTermTypes` imports `Effect4.Codegen.Target` and uses none of its
  declarations (the reference files).
- The nightly ingest lane fails its two pins above.
- The `Makefile`'s marker of `check-ingest` lists `tools/Drivers/Styles.lean` and
  `tools/Drivers/ForeignCorpus.lean` among its inputs, and not the moved module. It did not list
  `src/Effect4/Codegen/Styles.lean` either.

### Proposed decisions rows (proposals only)

- **P-CR9-1.** The `Makefile`'s rule `$(CHK)/ingest` lists `tools/Drivers/StyleSyntax.lean` among
  its inputs.
- **P-CR9-2.** The nightly ingest lane's pins move. The foreign file count becomes 22,419
  (`3bada1241`'s probe). The coverage key needs one of two repairs:
  - (a) the foreign corpus gains one program with a definition block;
  - (b) the key names `defs` and `invoke` as not constructed.

  Recommend (a): the foreign readers then meet a block.

## CR-8: one refusal alphabet, and refusals that name their site

### Base and head

Base `827252a85`; the slice's commit is the head.

### What landed, step by step

1. **The TypeScript reader's refusal type is generated from `ReadRefusal`** (DI-88's first step).
   - `TsGen` reads the inductive `Effect4.Program.ReadRefusal` off the environment it loads, and
     writes one TypeScript arm per constructor into `ts/eff/templates.gen.ts`
     (`readRefusalArms`, `tools/Drivers/TsGen.lean`). A field of a type with no carrier refuses
     the generation.
   - `ts/eff/read.ts` defines its `Refusal` as that type and its own three: `node`, `program`
     and `parse`. The hand type had seven of Lean's eight cases: it lacked `annotation`.
   - Three sites of the TypeScript reader now answer Lean's refusal, `annotation`. They are a
     loop's cursor type with no reading (`"local const"`), a fold's stated accumulator
     (`"fold accumulator"`), and a row's type argument with no reading
     (`"<spelling> type argument"`). Their five unit tests follow.
   - The compiler-backed foreign engine mirrors the fragment reader's refusal at a type argument
     (`ts/eff/ingest/ck.ts`). It now answers `annotation` too, so the two foreign engines still
     agree, and their test follows.
2. **`PrintRefusal.internalAction` gives up the block's refusals to seven named cases.** They
   are appended after the alphabet's others, so every older case keeps its wire tag:
   - `invocation (definition : Nat)`: an invocation with programs of a definition the signature
     lacks or that takes no program (`printInvoke`);
   - `emptyBlock`, and `bodies (position : Nat)` where declarations and bodies part
     (`printModuleWith`, `printDefsWith`);
   - `serviceName (name : String)`: a name two definitions, or two services' names, share;
   - `strayMethod (definition service : String)`: a method of a service the block lacks;
   - `service (name : String)` and `serviceMethod (service method : String)`: a service, or one
     of its methods, that does not print (`serviceFaultOf`, `methodType`, `methodClosure`).

   `serviceFault` and `serviceFaultOf` answer a refusal, not a string. `internalAction` keeps the
   template table's refusals and the typed print's sites. `RefusalsDerived` is regenerated, and
   the generator's guards sample the seven cases (`tools/Effect4Gen/guards/refusals.lean`).
3. **`SurfaceRefusal.unbound` names the reference and its scope.** It carries the unbound name
   and the names its scope binds, nearest first, less the builtins (`SourceBindings.scopeNames`).
   The lexical check's two other refusals get their own cases, `imports` and `lexical`
   (`lexicalRefusal`, `src/Effect4/Codegen/Admit.lean`).

### Changed files

- Core: `src/Effect4/Codegen/Refusal.lean`, `PrintLeaf.lean`, `Print.lean`, `SourceBindings.lean`,
  `Admit.lean` (all under `src/Effect4/Codegen/`); `src/Effect4/Laws/Codegen/Services.lean`.
- Regenerated: `src/Effect4/Api/RefusalsDerived.lean` (`python3 scripts/generate.py --only
  derived`) and `ts/eff/templates.gen.ts` (`--only ts`).
- Tools: `tools/Drivers/TsGen.lean`, `tools/Effect4Gen/guards/refusals.lean`,
  `tools/Tools/Code/Module.lean` (the boundary's refusals in words).
- The truth driver: `harness/truth/Truth.lean` (the new refusals in words).
- TypeScript: `ts/eff/read.ts`, `ts/eff/ingest/ck.ts`, `ts/eff/README.md`, and four test files
  under `ts/eff/test/` and `ts/eff/ingest/test/`.
- Batteries: `Test/Codegen/DefinitionsPrint.lean` (six new controls, one updated),
  `Test/Api/ApiContract.lean` and `Test/Codegen/PayloadClasses.lean` (the unbound name pinned).
- The contract: `Test/contracts/faces.contract.md`, a new amendment.

### Commands and results

Every `lake` and `make` command ran through the shared slot. The logs are in the seat's
scratchpad (`cr8/`, `gates/cr8/`, `gates/cr8b/`).

| Command | Result |
| --- | --- |
| `lake build` of the five edited core modules | passes: 128 jobs, 34 s |
| `python3 scripts/generate.py --only derived` | passes: `RefusalsDerived.lean` alone moves, by the seven cases and their samples |
| the narrow build (`cr8/build2.sh`): the edited modules, their direct importers, the codegen laws that unfold the printers, the tools and the batteries that read the refusals | first run: one battery failed, `Test/Codegen/PayloadClasses.lean`, at two guards that matched the old `.unbound`. After their repair it passes: 1,372 jobs |
| the refusal probe (`cr8/RefusalProbe.lean`) | each named case answers at a small program; the values that the batteries now pin |
| `python3 scripts/generate.py --only ts` | passes: `templates.gen.ts` alone moves, by the generated `ReadRefusal` |
| `make check-ts-reader`, first run | one test failed: the two foreign engines disagreed at an unreadable type argument. `ck.ts` mirrored the old detail; it now mirrors the new one |
| `make check-ts-reader`, after the repair | passes: 501 files, 416 matched, none mismatched, none refused with an oracle; 783 tests; tsgo's typecheck |
| `make check-gen`, before the commit | regenerates every group: the two files above are the only difference from the base commit, so the check fails until they are committed |
| `make check-gen`, after the commit `ae2765fd4` | passes: every Lean-only generated file is what its generator emits |
| `make check-host-protocol` | passes: the keyed differential's 57 runs, the scenarios, the to-do's service and the to-do on SQLite |
| `lake env lean --run harness/truth/Truth.lean` into the scratchpad | the truth manifest is byte-identical to the committed one |

### Axiom output

`#axiom_audit` over the five core modules, `RefusalsDerived`, `Effect4.Laws.Codegen.Services`
and the three edited batteries (`cr8/AuditCR8.lean`): 2,556 declarations within
`[propext, Quot.sound]`, none modulo a planned goal.

### Landed theorems and their placement

- `nodup_of_repeatOf` and `strayMethod_of_strayOf` (`src/Effect4/Laws/Codegen/Services.lean`):
  concept `exact-codecs`, steps of the claim `module-defs-round-trip` (R8). Their consumer is
  `serviceFault_none`, whose statement is unchanged. They replace the two `decide`-based steps
  of its old proof, since the fault now names what repeats and what strays.
- `readServiceMethods_ok` takes the service's name as an implicit argument. Its conclusion is
  unchanged.

### Lines removed and added

Without the two regenerated files, 106 lines removed and 362 added in 21 files. The regenerated
files add 114 lines and remove 5.

### Evidence

- Proved: the laws above, under `[propext, Quot.sound]`.
- Tested: the reader's 783 tests and its corpus run; the keyed lane; the batteries' new controls.
- Reproduced: the truth manifest, byte for byte; the two regenerated files by their producers.

### Open obligations

- The TypeScript reader answers Lean's refusal at three sites. Elsewhere it may name a refusal
  otherwise: an annotated function in a term row's place is one (`E4-CHECK-CE-017`). The
  generated reader of DI-88 closes the rest.
- The two foreign engines still answer `shape` at a loop's unreadable cursor type. Both reject it
  themselves, before the fragment reader, so they agree with each other and not with Lean's
  `annotation "local const"`.
- `internalAction` still names the template table's refusals and the typed print's sites by a
  string. Those are the table's data (`RowOut.refuse`) and the typed print's internal sites.

### Proposed decisions rows (proposals only)

- **P-CR8-1.** DI-88's register entry records that its first step landed: the refusal alphabet,
  generated from `ReadRefusal`.

## CR-7, resumed: the coordinator's option (a)

The coordinator ruled option (a) of `cr7-note.md` §4, in the note's §5 order. This section grows
with each part.

### Part 1: the repair of the TypeScript site printer

Base `ae2765fd4`; the part's commit is the head.

**The cause was not the one §3 of the note gave.** The note's probe paired an `iterate`'s
children with its argument positions. Paired correctly, every node's checked environment has
the length of its print depth. The refusing slot is a `catchIf`'s test under the row
`Effect.catch`, at `[1, 1, 1, 0, 0, 1]`. That row fixes the test to `true` and prints no hole for
it, so the template's depth for it is the node's own. The checker types it under the handler's
binder, one deeper. The note's §7 records the correction.

**The repair.** The site printer fits a slot's checked environment to the template's depth
(`PrintEliminators.atDepth`, `src/Effect4/Codegen/PrintEliminators.lean`). It cuts where the
checker's is longer, and pads with `unknown` where it is shorter. So no slot is refused for its
depth. The three leaf laws of the erasure read each term at its print depth through one
step, `atDepth_length`.

| Command | Result |
| --- | --- |
| the probe `cr7/EagerDepths.lean` | every node's checked length equals its print depth; one slot differs, the classifier above; the typed print now prints `timeout/eager` |
| `lake build` of the two edited modules and their direct importers | passes; the law module in 86 s |
| `lake env lean --run harness/truth/Truth.lean` into the scratchpad | the truth manifest is byte-identical, so no truth program used the fallback |
| `make check-host-protocol` | passes, with `timeout/eager` now printed typed |
| `make check-ts-reader` | passes: 501 files, 416 matched, none mismatched; 783 tests |
| `make check-corpus` | passes: 400 programs match the committed results |
| `#axiom_audit` of the two edited modules (`cr7/AuditCR7a.lean`) | 2,259 declarations within `[propext, Quot.sound]` |

The fallback in `shippedPieces` stays in this part. Part 2 removes it with the row-only printer.

### Part 2: the deletion stops at a decision boundary

**The one thing to know.** The site printer has no checked context in the main piece of a
program that shares a layer by reference. Deleting the row-only printer loses those modules: the
truth lane's `pDiamond` and two batteries' programs. The options and the recommendation are in
`cr7-note.md` §8.3. Nothing of part 2 lands. Part 1 stays as it landed.

Base `1807268cb`. This part commits the note's §8, this section and the patch, all under
`docs/research`. The patch applies to the base (`git apply --check`).

**What the patch holds**, by the note's §8.1:

- the row-only printer, its erasure and the fallback of `shippedPieces` deleted;
- the connector at the site printer, proved: a successful typed print under `NoJoin` is the print
  (`printTyped_eq_print`, by `plain_upTo`);
- `emitModule_complete` with the premise `typedMain`, and the counterexample battery of
  `E4-PRINT-CE-004` and `E4-PRINT-CE-005` (`cr7-part2/TypedPrintRefuses.lean`);
- a second repair: a spine reads no context, so an invocation's spine prints;
- the battery's port, the register rows, the claim's title and the two authority documents.

| Command | Result |
| --- | --- |
| `lake build Effect4.Laws.Codegen.PrintTyped`, the patch applied | passes, 73 s |
| `lake build` of its importers and the 32 batteries that emit a module, the patch applied | 30 pass. `Test.Codegen.ReadContract` fails at `nestedSharing`, and `Test.Api.ApiContract` at `sharedLayers` |
| the truth harness's `lake env lean --run`, the patch applied | stops at its two checks of `pDiamond`, before it writes a manifest |
| the probe `cr7/InvokeProbe.lean`, before the spine repair | an invocation's main piece refuses: no context at the spine's end, `[0, 1]` |
| the probe `cr7/LayerProbe.lean` | `nestedSharing`'s main piece has no environment at `[1]` and below; `typed:missing context` |
| `git apply --check cr7-part2/part2.patch` at `1807268cb` | applies |
| `python3 scripts/check-language.py --strict` on the note | passes |

**Axiom output.** None: no `#axiom_audit` ran over the patch, because it does not land.

**Lines.** The patch adds 2,026 lines and removes 2,074 (`cr7-part2/part2.stat`).

**Open obligations.** CR-7's deletion, its connector and its fusion wait on the ruling of §8.3.

**Evidence.** *Tested*: the builds and the three failing checks above, the patch applied.
*Assumed*: option (B)'s 800 to 1,000 lines, an estimate from the deleted row-only erasure.

**Proposed decisions row (proposal only).**

- **P-CR7-1.** A ruling among §8.3's three options. In (A) the checker types a layer reference
  by its target's type. In (B) the typed print prints a node with no checked context by the
  fold, and the fused erasure's plain instance covers it. In (C) the row-only printer stays. The
  seat recommends (C) now and (B) inside the fusion slice.

## The merge of the coordinator's branch

At the CR-7 boundary, as the coordinator asked, `refactor/phase1-phase3` (`69cbf348c`) is merged
into this branch at `5e19eff24`. The merge had no conflict. CR-2 and CR-6 start on its
`Makefile`, `scripts/generate.py` and `tools/Effect4Gen/manifest.json`.

## CR-2: the Lean producers that run the machine run native

**The one thing to know.** The truth manifest and the corpus manifest are written with the core
as native code, byte for byte as before. `check-truth` took 17 s and `check-corpus` 63 s.

Base `5e19eff24`; the slice's commit is the head.

### What landed

- **One helper.** `native_flags` (`scripts/generate.py`, beside `native_libraries`) gives the
  `--load-dynlib` flags of the native libraries that Lake loads for a Lean file's workspace
  imports. `scripts/lean-imports.py --dynlibs FILE...` prints them, and the `Makefile`'s
  `native_flags` reads them. `native_libraries` now queries Lake with nothing on stdout.
- **The producers that run the machine take them.** A file that runs the machine imports a module
  of `TestProgram` or `TestDogfood`, whose setups load the native core. They are the truth
  manifest (`gen-truth` and `scripts/check-truth.py`), the corpus manifest
  (`scripts/check-corpus.py`) and the printed corpus (`make corpus`).
- **The other producers stay interpreted.** The host protocol's, the schema fixtures', the
  codec's, the row types', the type vectors' and P2b's producers import no such module. Their
  imports load no native library, so the flags are empty there, and the recipes keep their text.
- **Each generation marker depends on the groups it reads.** `wire`, `cas`, `ts`,
  `host-protocol` and `schema-ts` wait on `derived`. `truth` waits on `derived`, `ts` and
  `host-protocol`, whose protocol its prelude imports. `census` waits on none. `docs/GENERATED.md`
  states the rule.

### Changed files

`Makefile`; `scripts/generate.py`, `scripts/lean-imports.py`, `scripts/lib/lean_imports.py`;
`scripts/check-truth.py`, `scripts/check-corpus.py`; `docs/GENERATED.md`.

### Commands and results

| Command | Result |
| --- | --- |
| `Truth.lean`, the truth manifest, interpreted and then native (`cr2/compare.sh`) | 68 s and 9 s; byte-identical, and equal to the committed `harness/truth/corpus.json` |
| `Truth.lean --corpus 400 4`, interpreted and then native | 60 s and 7 s; byte-identical |
| `tools/Drivers/Corpus.lean 400 4`, interpreted and then native | 3 s and 2 s; byte-identical, 408 programs kept |
| `make -n gen` | the host protocol's recipe runs before the truth lane's, and the truth recipe carries the flags |
| `make check-truth` | passes in 17 s: 81 programs agree, 12 signed divergences; the review measured 67 s |
| `make check-corpus` | passes in 63 s: 400 programs match the committed results; the review measured 112 s |
| `make check-host-protocol` | passes; 678 s, most of it the merged tree's first build |
| `make check-schema-codec` | passes in 6 s |
| `make check-target` | passes in 11 s: 104 resolved, none mismatching |
| `make check-ts-reader` | passes in 6 s: 783 tests |
| `python3 scripts/check-language.py --show docs/GENERATED.md` | no finding on the edited lines |

### Axiom output

None: no Lean source changed.

### Evidence

*Tested*: the gates and the byte comparisons above. *Measured*: the times, each run once through
the slot, on a machine with other seats.

### Open obligations

None. The lowering's LC-4 plans a compiled generator for the same reason, and this helper is the
one that it would share.

### Proposed decisions rows (proposals only)

- **P-CR2-1.** The review's P2, option (a), landed: the Lean producers that run the machine load
  the native core through one helper, `native_flags`. Option (b), `lean_exe` targets, waits on
  LC-4's compiled generator.

## CR-6: one fold of the target syntax, in the core

**The one thing to know.** The fold of the target syntax is generated into the core, and the
named erasure's call map is an algebra of it. `fold_of` refuses the four other traversals that
step 3 names, as written, so they stay hand traversals. The census's distance on the target
syntax is 11, not the 7 that the review projected.

Base `d3b702102`; head `fe523babb`, then `d4b034b5c` for the semantics report.

### What landed

- **The fold moves.** The manifest's group `TsFold` writes `src/Effect4/Codegen/TsFold.lean`, not
  `tools/Tools/Code/TsFold.lean`. The regenerated file differs from the old one only in its
  header's path. The code plane (`Tools.Code.TypeScript`) imports it from the core.
- **The hand fold goes.** `Effect4.Codegen.TargetFold` (205 lines) is deleted. The call map
  (`mapCalls`) is the generated `cata_expr` at one algebra (`callAlgebra`, over `CallCarrier`),
  in `src/Effect4/Codegen/EraseTermTypes.lean`.
- **The call map's equations.** The eleven `mapCalls_*` lemmas stay, proved from the generated
  fold. Each is a `rfl`, or one step through `atDepth_calls`, the list component read at one
  depth. `targetFold_exprs_map` goes, and `targetFold_properties` is `callAlgebra_properties`.
  The lemmas stay because 22 proofs name them, and inlining them would change those proofs'
  normal forms and remove nothing.
- **What does not land: step 3.** `fold_of` (`Effect4.Program.FoldOf`) refuses each traversal, at
  the file `cr6`'s probe wrote and removed:
  - `SourceBindings.exprUses`: its block has siblings over `List (String × Expr)` and
    `List (Nat × List Stmt)`, which no member of the family is;
  - `Metadata.readValue`: a case analysis on a child list's elements is no recursive call on an
    immediate child;
  - `Schema.reifyJson?`: its sibling `reifyJsonFields?` recurses on a field list's values, which
    is the same refusal.
- **Step 4, a proposal.** lean4-typescript v0.8.0 drops `scopedGen` and `scopedGenMasked`, and
  one object former takes a key form (P-CR6-1 below).

### Changed files

`tools/Effect4Gen/manifest.json`, `Makefile` (`DERIVED_OUT`); `src/Effect4/Codegen/TsFold.lean`
(moved from `tools/Tools/Code/TsFold.lean`), `src/Effect4/Codegen/EraseTermTypes.lean`,
`src/Effect4/Codegen/TargetFold.lean` (deleted), `src/Effect4/Laws/Codegen/PrintTyped.lean`;
`tools/Tools/Code/TypeScript.lean`; `docs/ARCHITECTURE.md`, `tools/view/README.md`.

### Commands and results

| Command | Result |
| --- | --- |
| `python3 scripts/generate.py --only derived` | passes; one new output, and no other derived file moved |
| `lake build` of the fold, the term eraser, the erasure, the law module and the code plane | passes; the law module in 95 s |
| `lake build` of `Test.Codegen.PrintTyped`, `Tools.Code.Module` and `Drivers.Emit` | passes |
| `#axiom_audit` of `Effect4.Codegen.TsFold`, `Effect4.Codegen.EraseTermTypes` and `Effect4.Laws.Codegen.PrintTyped` (`cr6/AuditCore.lean`) | 2,593 declarations within `[propext, Quot.sound]` |
| `#traversal_census TypeScript.Expr` under `Effect4` | 97 rows: 9 structural, 2 well-founded, 1 fold, 3 generated, 4 one-level |
| `make check-gen` | failed first, on `generated/semantics.md` alone: the merged branch's report was stale. After its re-cut (`d4b034b5c`) it passes |
| `make check-truth` | passes in 30 s |
| `make check-ts-reader` | passes: 783 tests |
| `make check-corpus` | passes in 63 s: 400 programs match |

### Axiom output

The three modules above are within `[propext, Quot.sound]`. The code plane `Tools.Code.TypeScript`
was audited too: 181 of its declarations reach `Classical.choice`, through the equation lemmas
of the package's `TypeScript.Render`. The axiom gate audits no `Tools` module, and this slice
changed only that module's import.

### Evidence

*Proved*: the call map's equations and the erasure law, unchanged in statement. *Tested*: the
gates above; no printed byte moved. *Measured*: the census.

### Open obligations

Step 3 waits on `fold_of`'s list-of-pairs siblings and its case analysis on a child list, or on
the traversals' rewriting as algebras.

### Proposed decisions rows (proposals only)

- **P-CR6-1.** lean4-typescript v0.8.0: `scopedGen` and `scopedGenMasked` go, and one object
  former takes a key form, so the target syntax's fold loses five arms.
- **P-CR6-2.** `fold_of` reads a sibling over a list of pairs and a case analysis on a child
  list's elements. Then `exprUses`, `stmtUses`, `readValue` and `reifyJson?` read as folds.
