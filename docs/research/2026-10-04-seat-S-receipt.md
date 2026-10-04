# 2026-10-04 seat S receipt: Σ_app steps 1 and 2 (the signature in the core, admission at Σ_app)

**The one thing to know before merging.** Admission is at Σ_app and `E4-TYPED-CE-041` is repaired,
with one deviation from the brief. The raw table's integer scan stays admission's first check and
refuses as `uninhabited at`, with the integer's path. `admitSig` runs second. Three owner-ruled
texts fix that refusal for a table:

- DI-67's ruled text: "`admitProgram` refuses a program or table mentioning it
  (`AdmitRefusal.uninhabited at`)";
- the frozen contract, `Test/contracts/foundation-wave2.contract.md:217-219`;
- decisions row 149 (a): "no contract revision".

So `admitSig`'s `intType` reason never reaches `admitProgram`. The certificate keeps the field
`intFreeTable`. `findIntInTable` stays, and its consumer is admission. `P5LedgerService.lean`'s pin
(`uninhabited ["table", "0", "answer"]`) holds, so neither the battery nor its row in
`Test/Dogfood/README.md` changed. The brief's variant, a table integer refused as
`signature (row i (intType column))`, needs the owner to revise DI-67, row 149 and the contract.
Proposed row 1 below has the options.

## Placement, written before the work (AGENTS.md)

The obligation of this slice is `lawfulSig_of_admitted` restated without its gap premise.

1. Concept: `residual-program-typing` (`docs/core/semantics.md`). Property: admission implies the
   typed state's lawful source.
2. Question: the claim `admitted-source-lawful` (role compatibility, R1), pointer
   `Effect4.Program.Typed.lawfulSig_of_admitted`. Its consumers are `AdmittedProgram.source`, then
   `reachable_typed_admitted` and `m7_admitted`.
3. Reach: any `SigApp`, declared services included. Judgment: program admission
   (`admitProgram`, `Program/Admission.lean`). Bounds: decisions row 21 (ruled: thread it), rows
   111–116, row 118 (flat carriers only), row 138 (M7 at the empty row table), DI-57.
4. Not established:
   - code generation at `app.signature` (step 4);
   - authoring at declared services (step 3); `Author.build` still admits at `⟨table, []⟩`;
   - M7 at a non-empty row table (R6, DI-57);
   - structured service carriers (row 118).
   The declared services are exercised only by tests until step 3.
5. Unlocks: step 4 (the faces at `app.signature`), and M6 for every admitted program with no
   premise (`reachable_typed_admitted`, R1).

## Base and head

| Tree | Branch | Base | Head |
| --- | --- | --- | --- |
| `/Users/pooks/Dev/lean4-effect4-sigapp` | `seat/sigapp` | `8ae01662` | the receipt commit, on `14d250ea` |

The commits, in order:

1. `54701843`: a fast-forward to `refactor/phase1-phase3` before the slice's commit (the
   coordinator's note: main moved, seat D's batteries).
2. `64a2cfc2`: the slice, steps 1 and 2.
3. `3917db93`: `refactor/phase1-phase3` at `46523f31` merged, with no conflict. The regenerated
   `generated/semantics.md` equals the textual merge byte for byte.
4. `14d250ea`: CE-041's green controls of admission at declared services.
5. This receipt, force-added.

Nothing is pushed.

## What landed

### Step 1: the signature in the core

- `src/Effect4/Program/SigApp.lean` (new) holds `SigApp` with `codeTy`, `builtinCodeTy`,
  `serviceTy` and `signature`. It also holds `Row.wellScoped`, `RowReason`, `rowChecks`,
  `ServiceReason`, `flatCarrierAlg`, `flatCarrier`, `serviceChecks`, `firstFailing`,
  `firstIndexed`, `firstDup`, `SigRefusal`, `sigRefusal?` and `admitSig`. Every fully qualified
  name is unchanged.
- `src/Effect4/Program/Columns.lean` (new) holds the column scans: `Path`, `findInt` with its
  companions, `inhabitedAlg`, `inhabited`, `admitColumn`, `internalHandleScan` and
  `findInternalHandle`. It sits below admission and the signature.
- `src/Effect4/Program/Ty.lean` holds the template profile beside `instantiate`, `infer` and
  `matchTemplate`: `Ty.varsOf`, `varsOfFields`, `varsOfItems`, `Ty.templateAdmissible`,
  `templateAdmissibleFields` and `templateAdmissibleItems`. `Row.wellScoped` cannot go there,
  because `Row` is declared in `Program/Eff.lean`, which imports `Program/Ty.lean`. It sits
  beside `rowChecks`, its one consumer.
- `LawfulSig`, `admitSig_ok_iff` and every theorem stay in `Laws/Program/Signature.lean` and
  `Laws/Program/Template.lean`, over the moved names. No second definition exists.

### Step 2: admission at Σ_app

- `AdmittedProgram (program : NativeEff) (app : SigApp)` extends
  `TypedProgram app.signature program`. Its fields are `intFreeTable`, `signature`
  (`admitSig app = .ok ()`), `formed` (at `app.rows`), `intFreeProgram`, `intFreeType` and
  `columnsType`. `signature` replaces `lawful`, `runnable`, `internalFreeTable` and
  `columnsTable`.
- `admitProgram program (app : SigApp := {})` runs, in order: the raw table's integer scan; then
  `admitSig app`, refused as the new `AdmitRefusal.signature (why : SigRefusal)`; then the program
  tree's integer scan, formation, typing at `app.signature`, and the inferred columns' integer and
  column scans.
- The order theorems are restated at `app`: `admitProgram_table_int`, `admitProgram_program_int`
  and `admitProgram_type_int`. `admitProgram_signature` replaces `admitProgram_table_internal` in
  place.
- The callers move through `⟨table, []⟩`: `Api.runAdmitted`, `Api.replayAdmitted`,
  `Api.Built.admitted`, `HostSession.Session.admitted`, `HostSession.start` and
  `Author.Internal.finishBuild`. `Run.lean` needed no change. The session header keeps the row
  table only (row 21, ruling 1).
- `harness/truth/session/Keyed.lean` calls `Api.admitProgram`, so it moves too. The brief does not
  name this file; it is a caller of the changed function.
- `Effect4.Api` exports `SigApp`, `SigRefusal`, `RowReason`, `ServiceReason`, `admitSig` and
  `admitProgram_signature`. `Api.Table` exports `lawful` only.

### The refusal variants deleted, and why each was unreachable

`admitSig` runs before every check that built these variants, and it refuses each condition
itself. The two facts are `admitProgram_signature` and `admitSig_ok_iff` (proved): a table that
fails a deleted check fails `LawfulSig`, so admission answers `signature why` first.

| Variant | Its old source | Where `admitSig` refuses the same condition |
| --- | --- | --- |
| `duplicateKey k` | `Table.checkLawful`'s repeated key | `SigRefusal.duplicateRow k` (`LawfulSig.rowsDistinct`) |
| `builtinCollision k` | `Table.checkLawful` | `rowChecks`' third check, `row i .builtinCollision` |
| `valueRowTrailing k` | `Table.checkLawful` | `rowChecks`' fourth check, `row i .valueRowTrailing` |
| `table why` | `checkTable` in admission | `rowChecks`' first two checks, `row i .notExternal` and `row i .notAsync` |
| `internalHandle at` | `findInternalHandleInTable` | `row i (.internalHandle "answer")` and `"error"` |

Before deleting each, I read every construction site in the tree: only the old `admitProgram`
built them. The build checks the deletion (tested): no remaining site constructs one.

Deleted with them, because their only consumer was admission or its laws:

- `Table.checkLawful` and its `findDup`, `Table.LawfulRefusal`, `findInternalHandleInTable` and
  `findEmptyColumnInTable`;
- `Table.findDup_eq_none_iff`, `Table.lawful_eq_true_iff`, `Table.checkLawful_eq_none_iff`,
  `Table.checkLawful_of_not_lawful`, `findEmptyColumnInTable_go_eq_none_iff` and
  `findEmptyColumnInTable_eq_none_iff`.

Kept, with their consumers:

- `checkTable` and `TableRefusal`. Their consumers are DI-61 (b)'s API surface (`Api.checkTable`),
  the dictionary's anchors for "formation", "row table" and "admission"
  (`docs/core/controlled-english.md`), `checkTable_none_externalRow`
  (`Laws/Program/Invocation.lean`) and `Test/Program/InvocationContract.lean`. The runner does not
  call it: it registers rows through `externalRow`. Proposed row 2.
- `checkTable_none_externalRow` is unchanged. It reads `checkTable`, not a certificate field, so
  the brief's move does not apply to it.
- `findIntInTable` and the field `intFreeTable`: DI-67, above.

### The bridge, replaced in place

- `lawfulSig_of_admitted (a : AdmittedProgram program app) : LawfulSig app` is
  `(admitSig_ok_iff app).mp a.signature`.
- `AdmissionGap` is deleted. `Laws/Program/Typed/AdmissionRows.lean` is deleted whole: none of
  its ten lemmas has a consumer left.
- `AdmittedProgram.source` and `reachable_typed_admitted` hold at any `app`, because
  `ProgramSource` takes the services and their lawfulness (`LawfulSig ⟨table, services⟩`).
- `m7_admitted` takes any `app` with the premise `app.rows = []` (`M7Fragment`'s
  `emptyTable`), and its root is `a.source`. The services may be declared.

### The consumers of the deleted fields

- `LawfulSig.registered` (new, `Laws/Program/Signature.lean`, next to `LawfulSig.tableLawful`):
  every row of a lawful signature is external and asynchronous. Consumer: `build_runnable`.
- `build_lawful` reads `LawfulSig.tableLawful`. `build_runnable` now states the row-wise
  registration fact that its docstring always described. `rebuild_admitted` is at
  `⟨before.table, []⟩`. All are in `Laws/Program/Author.lean`.
- `admitProgram_eq_ok` (`Laws/Program/CheckedTyping.lean`), and `admitProgram_certificate` and
  `admitted_unique` (`Laws/Run.lean`), are restated at `app`.
- `Typed/Membership.lean`'s private `foldr_orElse_eq_none` and `zipIdx_foldr_eq_none` stay.
  Their two-direction versions lived in the deleted `AdmissionRows.lean`, so nothing is left to
  fold them into. I edited only four docstring citations of moved definitions in that file.

### CE-041

- `Test/Counterexamples/Program/AdmissionUnserved.lean`: `admitProgram` refuses each witness with
  its signature refusal, by `decide +kernel`:
  - `refused`: `.signature (.unservedKey 0 appKey)`;
  - `refused_unscoped`: `.signature (.row 0 .notWellScoped)`;
  - `refused_union`: `.signature (.row 0 (.templateNotAdmissible "request"))`.
- `not_lawful` stays.
- Each old acceptance is a red control: a named `Bool` under `#guard_msgs (error)` with `#guard`.
  `decide +kernel` does not fit the union witness's red control. The kernel decides the refusal,
  but the elaborator's error message gets stuck on `Ty.sub`'s well-founded recursion (tested).
- Green controls exercise declared services (`14d250ea`):
  - `admitted_served`: clause 1's program is admitted once the application declares the key's
    carrier;
  - `admitted_reads_declared`: a read of the declared service types at `nat`;
  - `refused_reads_undeclared`: without the declaration the read is `illTyped`.
- `Test/Counterexamples/REGISTER.md`: `E4-TYPED-CE-041` is `REPAIRED 2026-10-04`, in the form of
  `E4-HOST-CE-008`'s row. The rows of `E4-TYPED-CE-015` and `E4-HOST-CE-007` name their new
  refusal form: the location is now the row and the column.
- `tools/Tools/SemanticsRegistry.lean`: the title of `admitted-source-lawful` no longer names the
  gap. `contestedBy` keeps `E4-TYPED-CE-041`, as `denote-typed` keeps its repaired rows. R1's
  first open part now names steps 3 and 4. The merge kept main's R4 change (`e40371c0`).

### Generated code and pins

- The Refusals group (`tools/Effect4Gen/manifest.json`) lists `RowReason`, `ServiceReason` and
  `SigRefusal` before `AdmitRefusal`. `python3 scripts/generate.py --only derived` regenerated
  `src/Effect4/Api/RefusalsDerived.lean` and `src/Effect4/Api/RunnerDerived.lean`.
- The guards cover the three new carriers: `tools/Effect4Gen/guards/refusals.lean` adds round
  trips, byte refusals, shape fits, byte distinctness and head agreement. Both
  `refusals.lean` and `runner.lean` name the new admission refusals.
- `Test/fixtures/proof-style/baseline.tsv` comes from `make record-proof-style`. Its diff has two
  parts:
  - the generated file's counts, 13 to 16 (`first` in `ofVal_exact`) and 20 to 23 (`simp` in
    `ofVal_toVal`), one per new carrier;
  - three entries removed, because `admitStraightProgram_*` now use `simp only`.
  No hand-written new use.
- `tools/Conform/Effect4/cases-policy.json` pins two new compiled case sites on `Ty` in the core:
  `Ty.varsOf` and `Ty.templateAdmissible`. Each pin is a default arm with the cover that
  `Ty.closed` and `Ty.instantiate` have.
- `Test/fixtures/baseline/` is untouched.

### The tests updated

`Test/Program/AdmissionColumns.lean`, `InvocationContract.lean`, `FormationContract.lean`,
`RecordTerms.lean` and `SignatureControls.lean` (a docstring); `Test/Api/ApiContract.lean`,
`HostSessionContract.lean`, `KeyedHostContract.lean` and `ExternalContract.lean`;
`Test/Run/RunContract.lean`; `Test/Counterexamples/Machine/Runtime/HostHandleForgery.lean` and
`LayerEnvironment.lean`; `Test/Counterexamples/Machine/Semantics/FitsOrder.lean`.

- `AuthorContract.lean` needed no change.
- The red control of CE-015 is kept: the old acceptance of the empty host column fails against
  `admitSig`.
- `HostHandleForgery.lean` keeps its nested-path controls on the column scan, with
  `findInternalHandle ["answer"]`.

`Api.readable`'s note in `src/Effect4/Api.lean` no longer says that the printer loses a scoped
fork's daemon flag. The printer refuses a child fork into a scope (`internalAction
"forkScoped:child"`, `Codegen/Templates.lean`), as seat D read. The coordinator asked for this
fix.

## Module status of the new files (decisions rows 200 and 202)

- `Program/Admission.lean` is not a Lean module because it imports `Program/Typed.lean`. That
  file is one of row 202's specialization sites; as a module it loses the machine's
  specializations, and the `lcnf` cut grows. Row 202 lists `Program.Admission` among the
  importers that stay non-module.
- `Program/Columns.lean` is not a module. `findInternalHandle` reads `internalHandleTargets`,
  which `Program/Typed.lean` defines beside the membership arms that read the same spellings. A
  module cannot import a non-module.
- `Program/SigApp.lean` is not a module, because it imports `Program/Columns.lean`.
- `Program/Ty.lean` stays a module. The template profile is ordinary structural recursion there.
- When row 202's seven files convert, `Columns` and `SigApp` can convert with them. They have no
  other non-module import.

Moving `internalHandleTargets` would let both new files be modules, but that definition is in the
LCNF closure of `api_gen.ml`. I kept it in place, and the LCNF cut has no diff.

## Commands and results

Every Lean command ran through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh` (two
threads).

| Command | Head | Result |
| --- | --- | --- |
| `lake build` (cache restore at the base) | `8ae01662` | 888 jobs, success |
| `lake build Effect4.Program.Admission` | working tree | 59 jobs, success |
| `lake build Effect4.Api.Author Effect4.Api.HostSession Effect4.Store.Domain.Derived.Program` | working tree | 139 jobs, success |
| `python3 scripts/generate.py --only derived` | working tree | PASS; `RefusalsDerived.lean`, `RunnerDerived.lean` written |
| `lake build Effect4 Effect4.Laws` | working tree | 641 jobs, success |
| `lake build` of the 20 touched tests | working tree | first run: the expected messages of four red controls in two files were wrong (fixed); second run: 512 jobs, success |
| `lake build Test` | working tree | first run: the ratchet refused the generated file's 3 + 3 new uses; after `make record-proof-style`, 893 jobs, success |
| `make check-cases` | working tree | first run: REFUSED, 2 unlisted (`Ty.templateAdmissible`, `Ty.varsOf`); after the pins, PASS, 213/213 |
| `lake build` | `3917db93` | 895 jobs, success |
| `make gen-semantics` | `3917db93` | no diff against the merge |
| `lake env lean -DwarningAsError=true Test/All.lean` | `3917db93` | exit 0 (lines below) |
| `make check-proof-style` | `3917db93` | exit 0; 1951 recorded uses, 60 unread commands, 1202 entries |
| `make check-cases` | `3917db93` | PASS, 213/213 subjects |
| `python3 scripts/generate.py --only derived --output-dir <scratch>` (verify) | `3917db93` | PASS: no file differs |
| `python3 scripts/generate.py --only lcnf` (in place) | `3917db93` | PASS; `git status` clean: the four LCNF artefacts are unchanged |
| `bash scripts/check-conservativity.sh 8ae01662 HEAD` | `3917db93` | PASS, 4 of 4 clauses; generated paths changed: `semantics.md`, `RefusalsDerived.lean`, `RunnerDerived.lean` |
| `lake build Tools.ProfileJson`, then `lake env lean -DwarningAsError=true harness/truth/session/Keyed.lean` | working tree | exit 0 |
| `lake build Tools.RowTypes` | working tree | success |
| `python3 scripts/check-language.py --strict docs/core/controlled-english.md AGENTS.md` | working tree | PASS |
| `python3 scripts/check-docs.py` | working tree | PASS, 72 documents |
| `lake build`; `make gen-semantics`; the gate | `14d250ea` | 895 jobs; report regenerated and committed; gate exit 0 |

The gate at `14d250ea`:

```
Effect4 library-root gate: 158 API/utility modules, 273 Laws-only modules; every library source is reachable; Effect4 never reaches Laws
Effect4 module and axiom gate: checked 656 modules and 80138 declarations; phases (ms): sources and closure 9, library roots 164, declarations 1973, resolution 496, axioms 12779, exemptions 240; semantic/test axioms are [propext,
 Quot.sound]; exact implementation boundary (17 module(s), 23 declaration(s)) additionally allows Classical.choice
Effect4 goal gate: 13 planned goal(s), each a theorem whose body is `sorry` outside the Effect4 root; 7 declaration(s) rest on goals; no other declaration reaches sorryAx
```

## Axiom output

`#print axioms` at `3917db93`, and at `14d250ea` for the three green controls:

| Declaration | Axioms |
| --- | --- |
| `Typed.lawfulSig_of_admitted`, `Typed.reachable_typed_admitted`, `Typed.m7_admitted`, `AdmittedProgram.source` | `[propext, Quot.sound]` |
| `LawfulSig.registered`, `LawfulSig.tableLawful`, `admitSig_ok_iff`, `admitSig`, `admitProgram` | `[propext, Quot.sound]` |
| `admitProgram_eq_ok`, `Run.admitProgram_certificate`, `Run.admitted_unique`, `Run.open_total` | `[propext, Quot.sound]` |
| `Authoring.build_lawful`, `build_runnable`, `rebuild_admitted`, `rebuild_self` | `[propext, Quot.sound]` |
| `admitProgram_table_int`, `admitProgram_signature`, `admitProgram_program_int`, `admitProgram_type_int`, `admitStraightProgram_admission_error`, `_ok`, `_outside` | `[propext, Quot.sound]` |
| CE-041's `refused`, `refused_unscoped`, `refused_union`, `not_lawful`, `admitted_served`, `admitted_reads_declared`, `refused_reads_undeclared` | `[propext, Quot.sound]` |
| `Ty.varsOf`, `Ty.templateAdmissible`, `Row.wellScoped` | none |

## Placement of each landed theorem

- `lawfulSig_of_admitted` (proved, restated in place): the placement above. It is the pointer of
  `admitted-source-lawful`, and it rests on no goal.
- `reachable_typed_admitted` (proved, restated): a top node of R1; M6 at the API at any `app`.
  It does not establish M6 at a host answer (answer-free tapes, row 95).
- `m7_admitted` (proved, restated): the claim `m7-admitted` (R9), concept
  `translation-simulation`, within `M7Fragment`. It does not establish M7 at a non-empty row
  table.
- `LawfulSig.registered` (proved, new): a step of `admitted-source-lawful`; consumer
  `build_runnable`.
- `admitProgram_signature` (proved, new in place of `admitProgram_table_internal`): admission's
  refusal order, exported by `Effect4.Api`. No proof consumes it, as none consumed the theorem it
  replaces.
- The other restated theorems keep their statements at the new index and their consumers.

## Proposed decisions rows (not written into the register)

1. **The table's integer refusal at Σ_app admission** (DI-67, row 149, the slice's step 2).
   - (a) Keep, as landed. The raw table's integer scan runs first and refuses as
     `uninhabited at`, with its path. `admitSig`'s `intType` never reaches `admitProgram`. The
     certificate keeps `intFreeTable`.
   - (b) The brief's design. `admitSig` runs first, and a table integer is
     `signature (row i (intType column))`. This revises DI-67's ruled text, row 149 (a) and
     `foundation-wave2.contract.md:217-219`. The path inside the column is lost. It changes
     `ApiContract.lean`'s `IntegerAdmission` pins, `P5LedgerService.lean`'s pin and its README
     row. It also deletes `findIntInTable` and `intFreeTable`.
   - Recommendation: (a). It keeps an owner-ruled refusal and its path, for one table scan.
2. **Retire `checkTable` and `TableRefusal`.** After step 2 no executable code calls them.
   `admitSig` answers the same question, located by row.
   - (a) Keep, as landed: the API's standalone registration check (DI-61 (b)).
   - (b) Retire them at step 3, when authoring runs `admitSig`. Move the dictionary's three
     anchors to `admitSig` and `rowChecks`, and amend DI-61 (b).
   - Recommendation: (b) at step 3. One condition should have one check.
3. **Where the signature's row reasons point.** `RowReason.internalHandle` and `emptyColumn` name
   the column, not the path inside it. The deleted table scans named the full path, for example
   `["table", "0", "answer", "inner"]`.
   - (a) Keep, as landed.
   - (b) Give `internalHandle` the scan's path, `internalHandle (at : Path)`.
   - Recommendation: (a), until an agent or a host needs the inner path.
     `E4-HOST-CE-007`'s row now says "at the row and the column".

## Open obligations

- The plan's steps 3–6 stay open. Step 2's note "Goal to state when the carrier lands:
  `AdmittedProgram.lawful : LawfulSig app`" needs no goal: `lawfulSig_of_admitted` states it,
  proved.
- These authority texts go stale with this slice. They are the coordinator's and the owner's
  files, so I did not edit them:
  - `docs/core/system-map.md`, R1's row: "admission and the faces (22 lines) stay pinned to the
    built-in signature". Admission no longer is.
  - `docs/core/controlled-english.md`: its Σ_app row cites `SigApp` at
    `src/Effect4/Laws/Program/Signature.lean`, where only its theorems remain. The two
    `inhabited` anchors cite `src/Effect4/Program/Admission.lean`; it is in
    `Program/Columns.lean` now. The anchor check passes, because the cited files still contain
    the words.
  - `docs/core/semantics.md` cites `inhabited` at `src/Effect4/Program/Admission.lean:79`.
  - `docs/core/traversal-census.md` §7 places `Ty.varsOf` and `Ty.templateAdmissible` at
    `Laws/Program/Template.lean`; they are in `Program/Ty.lean` now.
  - `docs/DESIGN-BASIS.md` cites `internalHandleScan` at `src/Effect4/Program/Admission.lean`;
    it is in `Program/Columns.lean` now.
  - `docs/STATE.md` says the bridge takes `AdmissionGap` as a premise.
  - `src/Effect4/Codegen/Read.lean`'s module note keeps the daemon-flag sentence that I removed
    from `Api.readable`.
- `admitProgram_eq_ok` (`Laws/Program/CheckedTyping.lean`) and `admitProgram_certificate`
  (`Laws/Run.lean`) state one fact twice. I restated both, so they are a cleanup candidate.

## What is bounded

- Every refusal and acceptance pin is a finite check (`#guard`, `decide +kernel`): tested. The
  bridge and the M6 and M7 statements hold at every `app`: proved.
- Declared services reach admission only through CE-041's three green controls (tested). No
  caller passes services until step 3.
- No host lane ran: TypeScript, the truth harness and `dune` did not run. `AdmitRefusal` is not
  on the wire: the conservativity check's alphabet clause passes, and the four LCNF artefacts
  regenerate without a diff (tested).
- The mirror census is not run by any target. I assumed it does not drift, from a read: neither
  `tools/Conform/Effect4/mirrors.json` nor `Test/fixtures/baseline/` names a declaration that
  this slice changes.
