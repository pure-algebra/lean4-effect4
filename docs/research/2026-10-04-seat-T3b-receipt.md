# 2026-10-04 seat T3b receipt: the read-modify-write rows carry binder terms

This receipt closes slices E and F of the state plan's T3b. It was written on 2026-10-05.
The design is `docs/research/2026-10-04-seat-T3b-design.md`. Its probes are in
`docs/research/2026-10-04-seat-T3b/`, and this phase's evidence is in
`docs/research/2026-10-04-seat-T3b/phase2/`.

## First: one gate of the brief is red, for a reason outside this seat

`bash scripts/check-conservativity.sh 917d4b5d HEAD` refuses clause C3. It names two rows of
`harness/truth/corpus-results.tsv`: `g158` and `g309`. The integration branch moved both rows in
`50700443` (the sweep of 2026-10-05) and gave them no `verdict_moves` name. This seat did not
change that file.

The evidence is tested:

- `bash scripts/check-conservativity.sh 917d4b5d 261b4a8e` refuses the same two rows. No commit of
  this seat is in that range.
- `bash scripts/check-conservativity.sh 261b4a8e HEAD` passes 4 of 4 clauses.
- `bash scripts/check-conservativity.sh --self-test` answers 22 of 22 controls.

I did not name the two rows in the policy. The policy is a review event, and the move is the
integration branch's. Proposed: the coordinator names `harness/truth/corpus-results.tsv:g158` and
`harness/truth/corpus-results.tsv:g309` in `verdict_moves`.

Follow these steps at the merge.

1. Merge `seat/t3b` by its head commit id.
2. Run `make gen-lcnf` on the merged tree. Never merge two generated `api_engine.ml` files by hand.
3. Merge the lists of the policy file by union.
4. Run `make check-cases`, then `make gen-semantics`, and commit the report.

The integration branch stands at `182312f3`. Since `261b4a8e` it changes seven files outside the
research notes: `docs/STATE.md`, `docs/UPSTREAM-BACKLOG.md`, `docs/core/decisions.md`,
`scripts/check-proofgraph-input.mjs`, `tools/Drivers/SemanticsControls.lean`,
`tools/Tools/ProofGraphView.js` and `tools/Tools/Semantics.lean`. This seat changes none of them.
A trial merge in memory is clean (tested: `git merge-tree --write-tree HEAD 182312f3`, exit 0).
The report's producer changed there, so step 4 is needed.

The main checkout also holds uncommitted work of another seat on the LCNF translator, read on
2026-10-05. It changes `src/OCaml5/Lcnf/`, `ocaml/gen/` and `ocaml/engine/api_engine.ml`. This
seat regenerates the same two OCaml files, so step 2 matters. This seat wrote nothing in the main
checkout, and pushed nothing.

## Base and head

| What | Commit |
| --- | --- |
| Base of the assignment | `917d4b5d` |
| Slice A: `syncOpOf` takes the point's environment | `e757a2f4` |
| Slice B: `ScopedOp.mapTerm`, `check_weaken` | `c7afee00` |
| Slice C: `Signature.termOf`, `bindTerm`, `checkRow` | `5abdb76f` |
| Slice D: `Signature.opAtLevel`, the generic faces | `15ee58c8` |
| Merge of the integration branch at `632265fd` | `44960c5b` |
| Slice E1: the names leave the stores | `648ea9db` |
| Slice E2: the groundwork of the cutover | `0ab2ef09` |
| Slice E3: the Lean cutover | `e112352f` |
| Slice E4: the estates, the policy | `861397bf` |
| Merge of the integration branch at `261b4a8e`, before the registry edit | `7c678efa` |
| Slice F: the acceptance programs, the registry, the documents | `1ff9a94a` |
| Slice E5: the ingest lane's foreign corpus | `1a76491b` |
| Slice F2: T2's lowerings kept as a control | `67e6ec20` |
| Head | the commit that adds this receipt, on `67e6ec20` |

Slice E is split into five green parts, as ruling D13 allows. E1 moves `FnName` to
`src/Effect4/Program/FnName.lean` and adds the images. E2 adds the term discharge, the term-row
lift and the family retirement of the conservativity check. E3 is the cutover of `NativeOp`. E4
regenerates the estates and ports the hand mirrors. E5 repairs the ingest lane.
The lcnf, eff, wire, ts and readme groups were regenerated at E4 only. The commits E1 to E3 are
green for the Lean build, and their OCaml and TypeScript estates are stale. Do not build the
estates at one of those three commits.

## What landed in slices E and F

- **The operations** (`src/Effect4/Program/Native.lean`). `NativeOp.refUpdateWith` …
  `refModifySomeWith (f : Term)` hold wire tags 24 to 31. Tags 5 to 12 are retired.
  `NativeOp.binder?` is the one view of an operation's term with its shape. The scope check,
  the weakening, `Signature.termOf` and the typed row all read it.
- **The store step.** `NativeOp.syncOpOf` hands the store the row's term with the node's
  environment. The term reads the cell's current value at the node's level and every outer binder
  below it.
- **The names** (`src/Effect4/Program/FnName.lean`). The five names are the faces' spelling of
  five terms per shape. `FnName.image` and `FnName.decode?` are an exact embedding at each shape
  and level. `NativeOp.atLevel` is the native signature's `opAtLevel`.
- **The typed row** (`src/Effect4/Laws/Program/Typed/Denotation.lean`). `termMaps_of_typed` and
  `bindTerm_termMaps` take a row's pre from the checker's typing of its term. `syncRow_typed`
  takes the node's typed environment. No planned goal was needed.
- **The keys** (`src/Effect4/Laws/Program/Handles/Term.lean`). `syncOpOf_keys` bounds a store
  operation's keys by the request's keys and the environment's.
- **The estates.** The engine's `env` argument is the point's environment carrier. The OCaml and
  TypeScript emitters print a term row's term. The TypeScript reader moves a row call to its
  node's level.
- **The acceptance programs.** p4 measures rc.112's program. p3 and p5 gain the parts that a
  binder term makes expressible.

### The moved programs

| Program | What moved | Evidence |
| --- | --- | --- |
| p4 (`Test/Dogfood/P4RateLimiter.lean`) | The measured program is rc.112's: one `Window` cell, one `Ref.modify` a request. It answers `[3, 2, 3]`, with or without a yield before the step. The stage loses `printed` and `readBack` until T5. The three-cell program is the race control: `[5, 0, 5]` with a yield between its read and its write | tested: `#guard`s on one decision tape |
| p3 (`Test/Dogfood/P3WorkerQueue.lean`) | The log's append is rc.112's `Ref.update` with a term. At a cell ascribed `ReadonlyArray<string>` it builds and runs. At `Ref<never[]>` the checker refuses it with `resultNotSubtype`. rc.112's `finish` builds as one `Ref.modify` that answers a boolean. The pool's stage does not move | tested |
| p5 (`Test/Dogfood/P5LedgerService.lean`) | The pure part of a deposit is one `Ref.modify` over the `Account` record. Its term captures the amount. The stage does not move | tested |

## The rulings, and where each landed

| Ruling | Where it landed |
| --- | --- |
| D1 (a) | `NativeOp` in `src/Effect4/Program/Native.lean`; `tools/Effect4Gen/wire-tags.json` |
| D2 (a) | `Signature.termOf` (slice C); `nativeSignature.termOf` reads `NativeOp.binder?`; `Row` is unchanged |
| D3 (a) | `nativeSignature_weakenNatural`; the red control is `weakenRequestOnly` (`Test/Program/ScopedOpContract.lean`) and `insertRequestOnly` (`Test/Codegen/FormsContract.lean`) |
| D4 (a) | `NativeOp.atLevel`, `NativeOp.atLevel_symm`; `nativeLawful.opAtLevel_symm` (`src/Effect4/Laws/Codegen/ReadLeaf.lean`) |
| D5 (b) | `FnName.image`; `FnName.decode?_image` (retraction); `FnName.image_of_decode?` (exactness); the agreement with T2's lowerings is `T2.image_agrees_lowering` (`Test/Program/ProgressContract.lean`), proved at `0ab2ef09` before E3 deleted T2's connector |
| D6 (a) | `family_retirements` in the policy; `scripts/lib/conservativity.py` clauses C2 and C3; controls R12 and G4; `wire-tags.json` keeps the family's tags |
| D7 (a) | `src/Effect4/Program/FnName.lean`; the name `Effect4.Machine.FnName` is kept |
| D8 (a) | `Test/Dogfood/P4RateLimiter.lean`; the README row says that the stage lost `printed` and `readBack` |
| D9 (b) | The gap is pinned in `Test/Program/FormationContract.lean` (see the open obligations) |
| D10 (a) | No goal. The red control is `pairUnion` in `Test/Program/TypedContract.lean`. `docs/core/semantics.md` §2.6 names `B` under `template-match-anchored`'s limit |
| D11 | Seven files outside the list were needed (see the departures) |
| D12 (a) | The claim `term-typed-maps` (`tools/Tools/SemanticsRegistry.lean`); its property line in `docs/core/semantics.md` §2.1 |
| D13 (a) | Eleven green slices: A to D, E1 to E5, F and F2 |

## The audit's two reminders

**The keys.** `syncOpOf_keys` states `o.keys ⊆ v.keys ++ env.flatMap Val.keys`.
`compileEff_keys` (`src/Effect4/Laws/Program/Handles/Compile.lean`) joins it with
`Point.env_keys_subset`. On the OCaml side the row `field Effect4.Machine.SyncOp.env E.t`
(`ocaml/engine/externs.txt`) makes the eight `env` arguments the point's carrier, and
`sh_ref_step` runs a term at `E.snoc env a`. The generator inferred
`carg Effect4.Program.NativeOp.syncOpOf 1 E.t` from the call sites, as the design assumed.

**The controls of P11**, each against the native rows:

| Control | Lean | OCaml and TypeScript |
| --- | --- | --- |
| An outer capture | `pRefUpdateCapture` answers `15` (`Test/Program/CompileContract.lean`); `native_capture_admitted` (`Test/Program/ScopedOpContract.lean`); `captureEnv` (`Test/Program/TypedContract.lean`) | `pCapture` answers `15` on both carriers (`ocaml/engine/test/test_engine.ml`) |
| The current value's scope | `native_current_admitted`; `pRefUpdateLevel` at level 2 answers `6` | `pLevel@2` answers `6` |
| The refusal out of scope | `native_out_of_scope_refused`; the checker's `binderTerm`; `pRefUpdateLevel` at level 3 has no type | `pLevel@3`: the step stops and the machine answers the unit |
| Weakening, and its broken map | `weaken_maps_term`, `unshifted_term_reads_the_slot`, `weakenRequestOnly`; `insertRequestOnly`; register row `E4-CHECK-CE-019` | — |
| `B` different from `A` | `pRefModifyOther` answers a string over a number cell; `pRefModifyDecide`; `modify_other_type_post` (`Test/Program/ProtocolPosts.lean`) | `pModifyOther` answers `"s"` on both carriers |
| Image round trips at several levels | forty images at levels 0 to 3 read back (`Test/Codegen/ReadContract.lean`) and print their names (`Test/Codegen/PrintContract.lean`) | `ts/eff/test/read.test.ts` at levels 0, 1 and 2; the reader lane matches 416 files |
| The faces refuse a term they cannot print | a capture, a composed term and an image at another level: `binderTerm` by the row's spelling, and not readable | `printVerdict` in the acceptance batteries |

A level control has a red side on both sides. The image one level down reads the outer binder:
`pRefUpdateLevel` at level 1 answers `11`, in Lean and in the engine.

## Changed files

Slices E and F change 111 files (`git show --name-only` over their seven commits). The list by
group:

| Group | Files |
| --- | --- |
| Core | `src/Effect4/Program/FnName.lean` (new), `Native.lean`, `Table.lean`, `Authoring.lean`, `src/Effect4/Machine/Stores.lean`, `src/Effect4/Store/Domain/ProgramWire.lean` |
| Laws | `Laws/Program/Typed/Denotation.lean`, `Typed/Residual.lean`, `Typed/Adequacy.lean`, `Typed/Commands/Clauses/Store.lean`, `Typed.lean`, `Progress.lean`, `Template.lean` (above seat T4's region), `Handles/Term.lean`, `Handles/Compile.lean`, `Authoring.lean`, `Authoring/Tactic.lean`, `Laws/Codegen/ReadLeaf.lean`, `Laws/Machine/Witnesses.lean` |
| Generated Lean | `Program/Authoring/Rows.lean`, `Laws/Program/Authoring/Rows.lean`, `Store/Domain/Derived/Program.lean` |
| Generators and tools | `tools/Effect4Gen/Rows.lean`, `manifest.json`, `wire-tags.json`, three guard fragments, `tools/Tools/ProgramStructure.lean`, `SemanticsRegistry.lean`, `RowTypes.lean`, `tools/Drivers/TsGen.lean`, `Styles.lean`, `ForeignCorpus.lean`, `tools/Conform/Effect4/cases-policy.json`, `tools/target/rows.ts`, `scripts/lib/conservativity.py` |
| OCaml, hand | `src/OCaml5/Eff/Emit.lean`, `Goldens.lean`, `World.lean`, `src/OCaml5/Tools/EffGen.lean`, `ocaml/engine/externs.txt`, `ocaml/engine/tools/api_engine_prelude.ml`, `ocaml/engine/e4_program.ml`, `e4_program.mli`, `ocaml/engine/test/test_engine.ml`, `ocaml/eff/test/prop_wire.ml` |
| OCaml, generated | `ocaml/eff/*` (types, wire, json, native, layout, manifest, structure, `pOps.bin`, `pOps.json`, `coverage.txt`), `ocaml/goldens/eff/*` (`pLoop.hex`, two manifests), `ocaml/engine/api_engine.ml`, `e4_program_layout.*`, `ocaml/gen/api_gen.ml`, two closure tables |
| TypeScript, hand | `ts/eff/read.ts`, `ts/eff/ingest/ck.ts`, `ts/eff/ingest/check-coverage.ts`, `ts/eff/test/read.test.ts`, `harness/truth/prelude.ts`, `harness/truth/Truth.lean` |
| TypeScript, generated | `ts/eff/eff.gen.ts`, `json.gen.ts`, `wire.gen.ts`, `profile.gen.ts`, `ts/eff/ingest/README.md` |
| Promoted tables | `generated/row-types.tsv`, `generated/row-citations.tsv`, `generated/semantics.md` |
| Batteries | 20 files under `Test/Program`, `Test/Codegen`, `Test/Machine` and `Test/Counterexamples`; `Test/Dogfood/Stage.lean`, `P3WorkerQueue.lean`, `P4RateLimiter.lean`, `P5LedgerService.lean` |
| Fixtures | the compatibility policy, `Test/fixtures/conservativity/mutations.json`, `Test/fixtures/proof-style/baseline.tsv` |
| Documents | `docs/core/semantics.md`, `Test/contracts/program-denotation.contract.md`, `Test/Counterexamples/REGISTER.md`, `Test/Dogfood/README.md` |

Not changed: `docs/core/decisions.md`, `lakefile.toml`, the root imports,
`Test/Audit/AxiomGate.lean`, the frozen baselines and seat T4's region of `Template.lean`.

## Commands and results

Every Lean command ran through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Every
result below is at `67e6ec20`, unless its row says otherwise. The last lines of each run are in
`docs/research/2026-10-04-seat-T3b/phase2/gates.txt`.

| Command | Result | Evidence |
| --- | --- | --- |
| `lake build` | exit 0, 904 jobs | proved, for the theorems it checks |
| `lake env lean -DwarningAsError=true Test/All.lean` | exit 0; the gate lines below | proved |
| `python3 scripts/generate.py --all --output-dir <scratch>`, then a byte comparison | 379 files, 0 differ; the README check passes (at `1ff9a94a`) | reproduced |
| `python3 scripts/generate.py --only lcnf`, then `git status` | no change (at `1ff9a94a`) | reproduced |
| `make check-gen` | PASS: every Lean-only generated file is what its generator emits | reproduced |
| `make check-cases` | conform cases: PASS | tested |
| `make check-proof-style` | exit 0: 1915 recorded uses; the baseline moves down by two, in a generated file | tested |
| `make check-ocaml` | exit 0; `gen-check: PASS` | tested |
| `dune test --force eff gen clock` and `dune test --force engine` | exit 0; `test_eff` 555 checks, `prop_wire` 6330, `test_lean_wire` 117, `test_engine` 132, 0 failures | tested |
| `make check-truth` | PASS: 38 programs agree on exits, schedules and sync exits; 1 signed divergence | tested, host-only |
| `make check-corpus` | PASS: 400 programs match the committed results; 25 registered disagreements | tested, host-only |
| `make check-target` | PASS: conformance 50 of 50; assignability 594 agree, 6 cut; rows 38 agree, 3 mismatch, 21 refused | tested, host-only |
| `make check-ts-reader` | exit 0: 447 files, 416 matched, 0 mismatched; `bun run typecheck` exit 0; 697 tests pass | tested |
| `bash scripts/check-conservativity.sh --self-test` | 22 of 22 controls | tested |
| `bash scripts/check-conservativity.sh 917d4b5d HEAD` | exit 1: C1, C2 and C4 pass; C3 refuses `g158` and `g309` (see the first section) | tested |
| `make check-slow` | exit 0, 909 jobs; 674 modules and 83907 declarations at the same axioms; no census pin moved | proved and tested |
| `make gen-semantics`, then `git status` | exit 0; no change | reproduced |
| `make check-semantics` | PASS: 34 report refusals, 18 register controls | tested |

TypeScript is checked by tsgo 7.0.0-dev.20260629.1 only. The host runs use effect 4.0.0-rc.112
under bun 1.4.2.

The gate lines of `Test/All.lean`:

- library-root gate: 163 API or utility modules, 275 Laws-only modules; `Effect4` never reaches
  the Laws graph;
- module and axiom gate: 665 modules and 81910 declarations at `[propext, Quot.sound]`;
- the exact implementation boundary: 17 modules and 23 declarations, with
  `Test/Audit/AxiomGate.lean` not edited;
- goal gate: 13 planned goals, and 7 declarations rest on goals.

No planned goal was added. The design's two fallback goals were not needed: `syncRow_typed` and
`nativeLawful` are proved.

Beside the brief's list I ran these, each exit 0: `make check-docs`, `make check-language`,
`make check-tsgo`, `make check-native`, `make check-host-protocol`, `make check-census`,
`make check-tools`, `make check-schema-codec` and `make check-schema-pins`.

## Axioms

`#print axioms` ran over every theorem whose declaration meets a line that this seat's eleven
commits wrote. The script reads `git blame` (`phase2/changed-lines.py`) and the environment
(`phase2/AxiomsOfChanged.lean`). The answer is in `phase2/axioms-of-changed.tsv`.

| Axiom set | Theorems |
| --- | --- |
| `[propext, Quot.sound]` | 152 |
| `[propext]` | 38 |
| none | 9 |
| any other axiom | 0 |

The 199 theorems cover slices A to F2. The axiom gate holds every other declaration.

## The placement of each theorem landed in slices E and F

The design's placement table covers slices A to D. The rows below are new or restated since.

| Theorem (file) | Concept, property | Claim, requirement | Consumer | Does not establish |
| --- | --- | --- | --- | --- |
| `termMaps_of_typed` (`Laws/Program/Typed/Denotation.lean`) | `store-typing`: the term relation's fundamental property for the term typer | `term-typed-maps`, R4 | `bindTerm_termMaps` | anything about a term that the checker refuses |
| `TermMaps.widen` (`Typed/Residual.lean`) | `store-typing` | a step of `term-typed-maps`'s use | `bindTerm_termMaps` | — |
| `bindTerm_termMaps`, `bindTerm_keeps`, `Ty.infer_keeps`, `Ty.matchTemplate_keeps` (`Typed/Denotation.lean`, `Template.lean`) | `residual-program-typing`: the row rule with the term's bindings | steps of `denote-typed`, R4 | `syncRow_typed` at the eight term rows | a row's post; a host row |
| `syncRow_typed` (restated with the typed environment) | `residual-program-typing`, serving `store-typing` | steps of `denote-typed` and `straight-meaning-typed`, R4 | `syncPerform_arm`, `inlineYield_typed`, `progress` | host rows (R6); concurrency: one store step is atomic in the model only |
| `FnName.decode?_image`, `FnName.image_of_decode?`, `FnName.image_injective` (`Program/FnName.lean`) | `exact-codecs`: an exact embedding of five names into terms, per shape and level | steps of `read_print` and `read_exact`, R8 | `NativeOp.atLevel_symm`, `nativeLawful.spell_row` | any term outside the images, which the faces refuse by name |
| `NativeOp.atLevel_symm` (`Program/Native.lean`) | `exact-codecs` | a step of `read_print` and `read_exact` | `nativeLawful` | lambdas (T5) |
| `nativeSignature_weakenNatural` (`Program/Native.lean`) | `initial-algebras-folds`: weakening over operation data | a step of `check_weaken` at the native signature | `effTy_insert` at native signatures; the forms' typing laws | substitution |
| `FnName.image_agrees` (`Laws/Program/Progress.lean`) | `translation-simulation`: a name's image computes the name's value | no claim; R4 | the faces' truth claim; `T2.image_agrees_lowering` | anything off the numbers: there a computing image stops |
| `syncOpOf_keys`, `compileEff_keys` (`Handles/Term.lean`, `Handles/Compile.lean`) | `reactive-scheduling`: the handle invariant | no claim | the compile's key invariant | that a term row steps |
| `performTerm_scoped` and the eight generated row lemmas | `initial-algebras-folds` | the authoring half of `operation-data-scoped` | `authoring_scoped` | term typing: scope is not typing |
| `NativeOp.row_wellScoped`, `NativeOp.rowKey_mem` (restated) | `subtyping-algebra`; `exact-codecs` | the native table's profile | none in `src`, `tools` or `Test` (tested, `grep`) | host rows, which carry no term |
| `progress`, `NativeOp.syncOpOf_cellImplements` (proofs only) | `store-typing` | `progress` at the `perform` node | the straight theorems | — |

## Departures from the design

1. **The names' meaning stays.** P7 deletes `FnName.total`, `partialUpdate`, `modify` and
   `modifySome`. I kept them and added `FnName.valueAt`. They are the right side of
   `FnName.image_agrees`, so the agreement on numbers is a theorem of the library.
2. **T2's lowerings stay as a control.** Ruling D5 (b) keeps the agreement with T2's images as a
   theorem. The library lost the lowerings at E3, as P7 directs. The battery keeps them as
   written, with `T2.lowering_agrees` and `T2.image_agrees_lowering`.
3. **Placement.** `FnShape`, the images and the decoder are in `Program/FnName.lean`, below
   `Native.lean`. `NativeOp.atLevel`, its law and `nativeSignature_weakenNatural` are in
   `Program/Native.lean`. The design's layout was circular.
4. **Two injectivity witnesses.** `FnName.headName?` and `FnName.totalName?` read a name off an
   image without its level. A direct `simp` proof reaches `Classical.choice`. Their case sites are
   pinned in the case-site policy, with notes.
5. **`modifySome` at `zeroWhenPositive`** is `pair(a, some(a))`, the value the name always meant
   there. D5 names the two re-imagings at the `update` shape only.
6. **`rowKey_mem`'s premise** is `(op.atLevel 0 0).isSome`: the operation's term is a face form.
7. **No `Test/Program/WeakenContract.lean`.** P11 names it, and no new battery file is allowed. The
   weakening controls are in `ScopedOpContract.lean` and `FormsContract.lean`.
8. **Slice C's reason.** A term with no type is refused as `binderTerm`, named by its row. The
   design passes the term's own refusal through. `resultNotSubtype` renders an unbound `B` as
   `never`.
9. **Seven files outside the design's list.** A gate forces each of the first five:
   - `tools/target/rows.ts`: the target lane spells a row by its name, which follows D1.
   - `tools/Tools/RowTypes.lean`: the probes now cover a row's answer, so `Ref.modify` is queried
     at `<"p0", "p1">` and answers `"p1"`.
   - `ts/eff/ingest/ck.ts`: the second ingest engine builds a row call itself and needs its own
     level move.
   - `tools/Drivers/ForeignCorpus.lean` and `ts/eff/ingest/check-coverage.ts`: the ingest lane
     read a profile operation as if every node were at level 0.
   - `generated/row-citations.tsv`: promoted by its tool, since the eight row names changed.
   - `harness/truth/prelude.ts`: comments only, for `FnName`'s new home.
10. **Additions inside `Test/Dogfood`.** P12 names p3 and p4. p5 also gains a part, its deposit,
    and `printVerdict` (`Stage.lean`) names a refused binder term.
11. **`harness/truth/Truth.lean`** gains the `binderTerm` arm that slice D left out. The file is
    outside the default build, so the omission did not show there.

## What is bounded or host-only

- **Proved**: every theorem of the placement tables, at `[propext, Quot.sound]`.
- **Reproduced**: every generated file against a fresh producer run; the truth corpus rendered from
  Lean is byte-identical to `harness/truth/corpus.json`; `generated/corpus-index.tsv` did not move.
- **Tested, finite**: every `#guard`; the forty images at levels 0 to 3; the OCaml and TypeScript
  tests; the conservativity controls.
- **Tested, host-only**: `make check-truth` (39 programs on rc.112), `make check-corpus` (400
  programs), `make check-target` and the reader lane. Five truth programs print
  `Ref.update(a0, incr)`. No truth program prints another shape or another name.
- **Bounded**: p4's `[3, 2, 3]` and its race control are runs on one decision tape. They say
  nothing about rc.112's scheduler.
- **tsgo's report on the eight rows** (`generated/row-citations.tsv`): at the probes each row's
  answer is exact, and the declared function type is the row's shape. The request column stays
  unjudged, as before.
- **The ingest lane**: I ran each step of `scripts/check-ingest.sh` by hand at `1a76491b`, without
  its `bun install --frozen-lockfile`. All pass: 22986 foreign fixtures on both engines, and
  23394 programs through the OCaml decoder.

## Open obligations

1. **The faces of a binder term (T5).** The faces print a term row only when its term is a name's
   image at the node's level. They refuse any other term by name.
2. **One identifier, one shape.** The TypeScript prelude has one function for each of the five
   names. The printer spells forty images. A printed `Ref.modify(ref, takeAndBump)` calls the
   total shape on rc.112. This finding is older than T3b, and T5 closes it.
3. **Operation data as a program annotation (D9 (b), row 212).** A record declaration inside a
   binder term is no program annotation. The term typer still checks its formation. The integer
   scan misses an `int` field that stays inside the program, and refuses one that reaches the
   program's answer. Both sides are pinned in `Test/Program/FormationContract.lean`.
4. **`B`'s completeness** where it first occurs covariantly is not claimed (D10).
5. **A stopped step in the machine.** When a term row's step stops, the compiled machine answers
   the thunk's pure value, the unit, and keeps the cell. The checker refuses such a program, and
   `progress` excludes it for a typed node. The behaviour is older than T3b; it is pinned as
   `pRefUpdateLevel` at level 3 and as `pLevel@3`.
6. **Concurrency.** One store step is atomic in the model. That says nothing about rc.112.

## Proposed decisions rows

The design's eight proposed rows stand. These join them.

- The names' meaning on values stays in the library as the right side of `FnName.image_agrees`.
  T2's lowerings stay in a battery, with their agreement, until T5 retires the names.
- A row's `name` follows its constructor, so the target lane and `generated/row-types.tsv` name
  the eight rows `refUpdateWith` … `refModifySomeWith`. A template row is probed at every
  parameter of its request, answer and error.
- The TypeScript reader reads a row call at its face and moves it to the node's level, as Lean's
  reader does. The second ingest engine keeps its own move.
- The ingest lane's coverage key of a row drops variable indices.
- Row 212 extends to binder terms, with the measured edge: the scan of the root's columns still
  refuses an `int` that reaches the program's answer.
- `verdict_moves` names `harness/truth/corpus-results.tsv:g158` and `:g309` (the sweep
  `50700443`).

## Found beside the assignment

Not repaired, and no table promoted:

- **`make check-tsdiag` is red.** Its harness copies `harness/truth/prelude.ts` without
  `prelude-atoms.gen.ts`, which the prelude re-exports. Every program then reports TS2305 or
  TS2724 on the atoms. The committed table has 363 rows at the base and at the head, and the
  corpus has 408 programs at both. The table was last promoted on 2026-09-17.
- **`lake build Effect4Gen`**, the library target, fails at the head: a build cycle with
  `Effect4GenNative`, and the 20 guard fragments, which have no imports. It is not a gate. The base
  has the same fragments and the same glob (read; not run at the base: assumed).
- **`make check-schema-ts` and `make check-kernel` were not run.** The first needs the pinned
  schema host, which neither checkout holds. The second is a sweep.
- **Stale lines for the coordinator.** `docs/core/system-map.md`, row R4, says "steps 3–5 open":
  step 5 is open. Decisions row 43 names `src/Effect4/Machine/Stores.lean` as `FnName`'s home: it
  is `src/Effect4/Program/FnName.lean`. `docs/STATE.md` at `261b4a8e` lists this seat's slices E
  and F as resumed.
- **Disk.** 13 GiB are free at the end, measured with `df -h /Users/pooks`.
