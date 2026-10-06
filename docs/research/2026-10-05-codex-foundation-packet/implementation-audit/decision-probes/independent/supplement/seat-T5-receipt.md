# 2026-10-05 seat T5 receipt: the faces of an operation's binder term

Status: receipt (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-t5-brief.md`, with the coordinator's addenda
1 to 4.

**The one thing to know before merging:** part A is landed whole, and part B is not landed. No
Queue program prints as a module yet. Each one still refuses at `Deferred.make`, by name
(`typeSpelling`). I stopped part B where the brief says to stop. It needs a reader of types that
the tree does not have: `Classes.readTy` reads no `never`. Item 9 is the design note.

Six more facts stand beside it.

- `make check-target` is red on this branch by one line that is not this slice's. The target
  selection lacks seat FOLD's `pFold`. With that one name added for a run, the lane is green
  (item 3).
- `make check-cases` refuses with eight stale lines. The policy names two functions that this
  slice deleted. I did not re-pin it (item 3).
- No planned goal is added. `read_print` and `read_exact` keep their statements and stay
  proved, at `[propext, Quot.sound]` (items 4 and 5).
- The five names left the foreign contract too. The constructed foreign corpus has 22314
  programs, where it had 22986 (item 7.7).
- Two printed steps and the rate limiter's request do not type-check under tsgo 7. The cause is
  on the target: `pair` and `tuple` keep a boolean or a number literal. I registered the
  difference with its control and did not repair it (item 7.10).
- The brief names three truth programs. One is in the lane, one is held out with its evidence,
  and one waits for part B. A fourth, a step of the Queue's probe, is added (item 7.9).

## 1. Base, head and steps

| Item | Value |
| --- | --- |
| Branch | `seat/t5`, in the worktree `/Users/pooks/Dev/lean4-effect4-t3b` |
| Base | `6214dcb8` |
| Step A1 | `d5559a5f`: the printer, the Lean reader, the laws, the pins that move |
| Step A2 | `cb9fcce9`: an annotated function at a term row is refused as an annotation (addendum 2) |
| Step A3 | `f14f2d33`: the names' bridge goes; the generators follow |
| Step A4 | `f2760046`: the battery `Test/Codegen/TermRows.lean` |
| Step A5 | `6507d08e`: the TypeScript reader, the two foreign recognizers, the generated tables |
| Step A6 | `9a92bf86`: the two choices, with their compiler control |
| Step A7 | `5773ffb2`: the prelude's five functions go; two truth programs |
| Addendum 3 | `23d7efbe`: the pinned truth check compiles the tuple control |
| Addendum 4 | `2deea521`: a term row with explicit type arguments is refused by both foreign readers |
| Step A8 | `6065591a`: the contract's amendment, R4's row, the property line |
| A comment | `71551c9f`: the styles driver's probe comment |
| Head | the commit that adds this receipt, on `71551c9f` |

Nothing is pushed. `git diff --stat 6214dcb8..71551c9f` counts 114 files: 72 written or
regenerated outside `harness/truth/generated`, and that folder's 42 modules.

## 2. Changed files, by group

| Group | Files | What changed |
| --- | --- | --- |
| Signature | `src/Effect4/Program/Typing/Rules.lean`, `src/Effect4/Program/Native.lean`, `src/Effect4/Program/Table.lean` | `Signature.withTerm` and `Signature.face` replace `opAtLevel`; a term row has no trailing name; `NativeOp.spelled` holds 23 operations; `NativeOp.rowKey_mem` restated |
| Printer | `src/Effect4/Codegen/PrintLeaf.lean`, `src/Effect4/Codegen/Templates.lean`, `src/Effect4/Codegen/Print.lean` | `withFunction`, `printPerform`; the row-call template calls it |
| Lean reader | `src/Effect4/Codegen/Read.lean` | `lastArgument?`, `splitFunction`, `installTerm`, `termFree`, `functionAnnotation`, `readPerform`, `termReadable`; five fields of `LawfulSpelling` |
| Classes | `src/Effect4/Codegen/Classes.lean` | the record collector reads an operation's term (`ScopedOp.term?`) |
| Laws | `src/Effect4/Laws/Codegen/ReadLeaf.lean`, `src/Effect4/Laws/Codegen/ReadPrint.lean`, `src/Effect4/Laws/Codegen/PrintReadable.lean`, `src/Effect4/Laws/Program/Progress.lean` | item 5; one docstring in the last file |
| Names | `src/Effect4/Program/FnName.lean`, `src/Effect4/Codegen/Forms.lean`, `src/Effect4/Codegen/Styles.lean` | item 6 |
| Atoms | `src/Effect4/Machine/Term.lean`, `src/Effect4/Program/NativeAtom.lean` | the prelude signature of `cons`, and its citation (item 7.2) |
| Root | `Test/All.lean` | one line after `import Test.Codegen.RecordTerms` |
| Tests | `Test/Codegen/TermRows.lean` (new), `Test/Codegen/PrintContract.lean`, `Test/Codegen/ReadContract.lean`, `Test/Codegen/FormsContract.lean`, `Test/Program/FoldContract.lean`, `Test/Program/AuthorContract.lean`, `Test/Program/InvocationContract.lean`, `Test/Program/Gen.lean` | the battery; the pins that move; two counts; one docstring |
| Dogfood | `Test/Dogfood/Stage.lean`, `Test/Dogfood/P3WorkerQueue.lean`, `Test/Dogfood/P4RateLimiter.lean`, `Test/Dogfood/P5LedgerService.lean` | pin lines and each battery's `stage`, and nothing else |
| Tools | `tools/Drivers/TsGen.lean`, `tools/Drivers/ForeignCorpus.lean`, `tools/Drivers/Styles.lean`, `tools/Tools/RowTypes.lean`, `tools/Tools/SemanticsRegistry.lean`, `src/OCaml5/Tools/EffGen.lean`, `src/OCaml5/Eff/Emit.lean` | 23 rows; the lambda shapes with their terms; a term row is no callable adapter row; R4's row |
| TypeScript, hand | `ts/eff/read.ts`, `ts/eff/ingest/ck.ts`, `ts/eff/ingest/oxc.ts`, `ts/eff/ingest/check-coverage.ts`, `ts/eff/ingest/check-corpus.ts`, `ts/eff/ingest/fidelity/roundtrip.ts`, four test files, `ts/eff/test/term-rows.test.ts` (new) | the reader's function form; the foreign function form; the pinned foreign count |
| Truth lane | `harness/truth/Truth.lean`, `harness/truth/prelude.ts`, `harness/truth/run-truth.ts`, `harness/truth/term-rows.typecheck.ts` (new), `harness/truth/tsconfig.json`, `harness/tsdiag/run-tsdiag.mjs`, `scripts/check-truth.py`, `Makefile`, `Test/fixtures/target/selection.json` | two programs; no function name in the prelude; the compiler control and its wiring; addendum 3 |
| OCaml, hand | `ocaml/eff/test/prop_wire.ml`, `ocaml/eff/README.md` | one comment; one stale count removed |
| Generated | `ts/eff/profile.gen.ts`, `ts/eff/forms.gen.ts`, `ts/eff/ingest/README.md`, `ocaml/eff/eff_native.ml`, `harness/truth/prelude-atoms.gen.ts`, `harness/truth/corpus.json`, `harness/truth/result.json`, `harness/truth/result.md`, `harness/truth/generated/`, `generated/corpus-index.tsv`, `generated/row-types.tsv`, `generated/row-citations.tsv`, `generated/semantics.md` | item 3 names what moved in each |
| Documents | `Test/contracts/faces.contract.md`, `docs/core/semantics.md`, this receipt | the amendment of 2026-10-05; two sentences of one property |

## 3. Commands and results

Each Lean or Lake command ran through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`,
written `SLOT` below. Each `make` took `-o build -o ts/eff/node_modules`, and the truth targets
took `-o harness/truth/node_modules` too. Each command ran on the head's tree unless the row
says otherwise.

| Command | Result | Evidence |
| --- | --- | --- |
| `SLOT lake build Effect4 Effect4Laws Test Tools OCaml5` | exit 0, 958 jobs. It holds the default `lake build`. The gate lines are below the table | proved, for the laws; tested, for the batteries |
| `SLOT lake env lean Test/Audit/ProofStyle.lean` | exit 0; `1920 recorded uses and 60 recorded unread commands in 1178 entries`. The baseline is unchanged | tested |
| `SLOT python3 scripts/generate.py --only F`, for `F` in derived, lcnf, eff, wire, cas, ts, readme | each `PASS generate`. `git status` after them: five files moved, named below | reproduced |
| `SLOT make corpus` | `kept 408 (readable 385) refused 0` | reproduced |
| `opam exec --switch=effect4 -- dune build`, in `ocaml/` | exit 0 | tested |
| `opam exec --switch=effect4 -- dune test --force eff gen clock` | exit 0; `test_lean_wire: 117 checks, 0 failures`; `test_eff: 619 checks, 0 failures`; `prop_wire: 6345 checks, 0 failures (seed 42)`; `test_val_frames: 26 checks, 0 failures`; `metadata: 207 checks passed` | tested |
| `opam exec --switch=effect4 -- dune test --force engine` | exit 0; each suite ends `ALL PASS: 0 failure(s)`; each program is `Fast = Ref, whole report` | tested |
| `SLOT make check-truth` | exit 0; host tests `23 pass, 0 fail`; `PASS: 41 programs agree on exits, schedules and sync exits; 1 signed divergence(s)`; `PASS truth: … the regenerated modules type-check` | tested, host-only |
| `SLOT make check-ts-reader` | exit 0; `files 450: matched 416, mismatched 0, refused with oracle 0, accepted without oracle 27, refused without oracle 7`; tsgo exit 0; `713 pass, 0 fail` | tested, host-only |
| `SLOT make check-target`, as committed | exit 2. `PASS row-types`. `bun test tools/target`: `27 pass, 1 fail`. The failing test expects `program/pFold`, which the selection lacks | tested, host-only |
| `SLOT make check-target`, with `"pFold"` added to the selection for the run and removed after it | exit 0; `28 pass, 0 fail`; `target conformance [effect@4.0.0-rc.112/adapter]: PASS; 53 expected, 53 attempted, 53 resolved, 0 mismatching, 0 refused`; `PASS assignability`; `PASS rows` | tested, host-only |
| `SLOT python3 scripts/check-conform.py compiler` | `conform compiler: PASS, exit 0` | tested |
| `SLOT make check-cases` | `conform cases: REFUSED, exit 1`. The eight lines are below | tested |
| `SLOT make gen-semantics` | exit 0; `generated/semantics.md` written. It counts 326 proved claims before and after | reproduced |
| The steps of `scripts/check-ingest.sh` by hand, without its install step | each `PASS`; listed below | tested, host-only |

The gate lines of `Test/All.lean`, from the head's build:

```text
Effect4 library-root gate: 165 API/utility modules, 278 Laws-only modules; every library source is reachable; Effect4 never reaches Laws
Effect4 module and axiom gate: checked 676 modules and 83511 declarations; … semantic/test axioms are [propext, Quot.sound]; exact implementation boundary (17 module(s), 23 declaration(s)) additionally allows Classical.choice
Effect4 goal gate: 14 planned goal(s), each a theorem whose body is `sorry` outside the Effect4 root; 7 declaration(s) rest on goals; no other declaration reaches sorryAx
```

The atom table is in a bottom module, so its change rebuilt the whole tree once:
`real 1361.92` seconds at two threads.

**The generated groups.** The producers moved five files: `ts/eff/profile.gen.ts`,
`ts/eff/forms.gen.ts`, `ts/eff/ingest/README.md`, `ocaml/eff/eff_native.ml` and
`harness/truth/prelude-atoms.gen.ts`. Every other output is byte-identical: the derived Lean
modules, the four LCNF artefacts, the wire goldens, the CAS goldens, and the golden programs
with their `.ty` verdicts.

**The corpus index.** The printed length moved on 39 programs, each of which holds a term row.
The sum of the moves is 463 characters. No verdict moved, in any column. The 39 names:
`g18 g26 g45 g61 g63 g76 g90 g94 g101 g108 g124 g125 g126 g127 g147 g154 g156 g166 g169 g170
g191 g197 g198 g231 g239 g246 g248 g254 g255 g259 g265 g294 g298 g315 g345 g357 g364 g379
pLoop`. The conservativity policy will meet these.

**The truth group.** It holds 42 programs. Every module's import header moved, `pLoop` prints
its row with a function, and two modules are new. No tape moved.

**The refusal of `make check-cases`.** The policy decides two functions that are gone. No
other subject is refused, and no default arm took in a new case.

```text
refused lcnf.cases.stale caseSite:Effect4.Program.Lit/Effect4.Machine.FnName.totalName?/0: …
refused lcnf.cases.stale caseSite:Effect4.Program.Term/Effect4.Machine.FnName.headName?/0: …
refused lcnf.cases.stale caseSite:Effect4.Program.Term/Effect4.Machine.FnName.headName?/1: …
refused lcnf.cases.stale caseSite:Effect4.Program.Term/Effect4.Machine.FnName.headName?/2: …
refused lcnf.cases.stale caseSite:Effect4.Program.Term/Effect4.Machine.FnName.headName?/3: …
refused lcnf.cases.stale caseSite:Effect4.Program.Term/Effect4.Machine.FnName.headName?/4: …
refused lcnf.cases.stale caseSite:Effect4.Program.Term/Effect4.Machine.FnName.totalName?/0: …
refused lcnf.cases.stale caseSite:Effect4.Program.Term/Effect4.Machine.FnName.totalName?/1: …
conform-cases: 237/237 subjects, 229 pass, 8 refused, 0 counterexample, 0 unresolved, exit 1
```

Each line ends: "the policy decides `…` on `…`, but the scan found no case site there: the
function is gone, was renamed, or no longer matches on this family".

**The red steps of `make check-target` at the base.** Seat FOLD did not run this lane. Three
things were stale. Two are generated files, and I regenerated them: each gains three lines,
and each line is one of FOLD's atoms (`take`, `drop`, `sameHandle`). They are
`generated/row-types.tsv`, whose producer this slice changes, and
`generated/row-citations.tsv`, which reads it. The third is a hand fixture, and I left it:
`Test/fixtures/target/selection.json` lacks `"pFold"`. Its place is after
`"pInterruptEscape"` and before `"pModifyFold"`, which is the corpus's order.

**The ingest gate's steps.** `make check-ingest` is not in the brief's list. This slice changes
that lane, so I ran each step of its script by hand. I left out its `bun install` step, which
the brief forbids.

```text
PASS oracle coverage: 25 Eff, 6 statements, 11 actions, 10 layers, 54 native rows; 19 forms at four depths
PASS printed: 408 exact JSON/wire comparisons on each parser with shared form lowering; batch bound 500
PASS foreign: 22314 exact JSON/wire comparisons on each parser with shared form lowering, exact key tables and complete verdict agreement; batch bound 500
PASS inclusion: 408 printed modules, 323 lifted by both engines to the printed oracle up to service-key renumbering; … 85 refused by the foreign contract: … E-ARG-DYNAMIC … x21, … E-FAIL-NOT-DOCUMENTED … x61, … E-REF-UNBOUND … x3
PASS source edits: printed, 408 fixtures × 6 transformations × 2 engines; …
PASS source edits: foreign, 22314 fixtures × 6 transformations × 2 engines; …
PASS source edits: negative, 22 fixtures × 6 transformations × 2 engines; …
PASS source edits: negative, 2 fixtures × 6 transformations × 2 engines; …
PASS ingest README: generated tables match
PASS OCaml exact decoder and JSON oracle: 22722 programs
PASS fidelity: four original/reprinted programs agree; requirement, foreign import and v3 exclusions hold; poisoned rerun reuses no old observations
```

The inclusion line equals the one that seat T3b recorded: 323 lifted and 85 refused. Of the 39
programs with a term row, 23 are lifted and 16 are refused. A refused one is refused for
another node of the program, such as a failure that is no literal.

### Not run

The brief excludes each command of the first list. Each is **not run**.

- `make check-gen`
- `make check-slow`
- `make check-corpus`
- `bash scripts/check-conservativity.sh`
- `make gen-truth-ledger`
- `make check-truth-release`

These are not run either, and no result of theirs is claimed.

- `make check-ingest` as a target. Its steps ran by hand, as above.
- `make check`, `make check-full`, `make check-native`, `make check-ocaml`, `make check-docs`,
  `make check-language`, `make check-semantics`, `make gen-tsdiag`.
- The three commands that the brief names as red before this slice: `make check-tsdiag`,
  `make check-schema-ts` and `lake build Effect4Gen`.

`harness/truth/build-ledger.tsv` and its run record are unchanged. They are stale by three
programs now: `pFold`, `pModifyFold` and `pQueueOffer`.

### Refused tool calls

A guardrail hook refused three of my commands in this session. Each sent a stream to
`/dev/null` on a line that named Lean. I ran each again without the redirection. No step was
skipped for it.

## 4. Axiom output and plan status

The axiom gate holds every declaration at `[propext, Quot.sound]`. `Test/Codegen/TermRows.lean`
prints the first nine lines below by `#print axioms`, and a scratch file printed the rest.

```text
'Effect4.Program.read_print' depends on axioms: [propext, Quot.sound]
'Effect4.Program.read_exact' depends on axioms: [propext, Quot.sound]
'Effect4.Program.readPerform_printPerform' depends on axioms: [propext, Quot.sound]
'Effect4.Program.readPerform_exact' depends on axioms: [propext, Quot.sound]
'Effect4.Program.withFunction_of_splitFunction' depends on axioms: [propext, Quot.sound]
'Effect4.Program.splitFunction_withFunction' depends on axioms: [propext, Quot.sound]
'Effect4.Program.splitFunction_printRow' depends on axioms: [propext, Quot.sound]
'Effect4.Program.printPerform_ok' depends on axioms: [propext, Quot.sound]
'Effect4.Program.nativeLawful' depends on axioms: [propext, Quot.sound]
'Effect4.Program.withFunction_printRow' depends on axioms: [propext, Quot.sound]
'Effect4.Program.NativeOp.rowKey_mem' depends on axioms: [propext]
'Effect4.Program.roundTrip_eq' depends on axioms: [propext, Quot.sound]
```

The `#plan_status` lines:

```text
Effect4.Program.read_print: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
Effect4.Program.read_exact: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
Effect4.Program.readPerform_printPerform: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
Effect4.Program.readPerform_exact: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
Effect4.Program.nativeLawful: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
```

## 5. Each landed theorem's placement

No planned goal is added, and none is proved. The slice's obligation is the first row of the
brief's table.

- **Concept:** `translation-simulation`.
- **Question:** R8's top nodes `read_print` and `read_exact`. The registry has no separate
  claim for them. They also close a part of R4's first open part, whose text I rewrote.
- **Reach:** every program whose term rows are scoped one level up, covered and unannotated,
  on a row that is no value row. The printed syntax is read by the Lean reader. The premise
  `LawfulSpelling sig spell` stands, and `nativeLawful` discharges it for the native profile.
- **It does not establish:** a host run, the target's type of a printed term, a stated type,
  or a row's type arguments. The truth lane tests finite programs only.
- **It unlocks:** the printed form of p3, p4 and p5, whose stages now say `printed` and
  `readBack`, and the printed form of each Queue step. It does not yet unlock a Queue module.

| Theorem | File | What it states | Its consumer |
| --- | --- | --- | --- |
| `read_print`, `read_exact` | `src/Effect4/Laws/Codegen/ReadPrint.lean`, `src/Effect4/Laws/Codegen/Read.lean` | Unchanged statements. Each gains its case at a term row | R8's top nodes |
| `readPerform_printPerform` | `src/Effect4/Laws/Codegen/ReadLeaf.lean` | A printed row call reads back to its `perform`, at a readable request and a readable term | `readRow_rowCall_print`, the row-call step of `read_print` |
| `readPerform_exact` | the same file | What `readPerform` accepts prints back to the tree it read | the row-call arm of `read_exact` |
| `splitFunction_printRow`, `splitFunction_call_none`, `splitFunction_method_none`, `binders_read_idents`, `binders_read_printTupleArgs`, `binders_read_printMethodArgs` | the same file | A printed row call without a function ends in no function of the node's binder | `readPerform_printPerform`, at a row with no term |
| `splitFunction_withFunction`, `withFunction_printRow`, `withFunction_of_splitFunction` | the same file | The split inverts the append, in both directions | the two theorems above |
| `LawfulSpelling.face_row`, `LawfulSpelling.face_of_none` | the same file | A face has its operation's row; an operation with no term is its own face | the row lemmas, which now conclude at `sig.face op` |
| `nativeLawful`, `NativeOp.row_hygiene` | the same file | Reproved. `nativeLawful` gains five fields on `withTerm` | every native use of the two round-trip laws |
| `withFunction_head`, `printPerform_head`, `printPerform_nodeLike` | `src/Effect4/Laws/Codegen/ReadPrint.lean` | A printed row call keeps the row's head | `earlier_none_rowCall`: no earlier template reads it |
| `printPerform_ok` | `src/Effect4/Laws/Codegen/PrintReadable.lean` | A readable row call prints | `roundTrip_of_readable` |
| `print_perform` | `src/Effect4/Codegen/Print.lean` | `print` at a `perform` is `printPerform`, by `rfl` | the row-call steps |
| `NativeOp.rowKey_mem` | `src/Effect4/Program/Table.lean` | A built-in operation's row key is a built-in key, at any term | the table's collision check |

`LawfulSpelling` gains five fields (`src/Effect4/Codegen/Read.lean`): `withTerm_row`,
`termOf_withTerm`, `withTerm_termOf`, `withTerm_withTerm` and `withTerm_none`. Its field
`spell_row` now answers the face. A signature whose operations carry no term meets the five by
`rfl`, with the default `withTerm`.

## 6. Each deleted declaration, and each reader found

The brief asks for a search before each deletion. The table gives each reader that I found
and what became of it.

| Deleted | Where | Its readers, and what became of each |
| --- | --- | --- |
| The field `Signature.opAtLevel` | `src/Effect4/Program/Typing/Rules.lean` | `nativeSignature`, and the reader's `atNodeLevel`. Both use `Signature.withTerm` now |
| `atNodeLevel` | `src/Effect4/Codegen/Read.lean` | `readPerform`. It installs the term with `installTerm` |
| `NativeOp.termFace`, `termFace_some`, `termFace_none` | `src/Effect4/Program/Native.lean` | `NativeOp.row`, whose term rows have no trailing name now; `NativeOp.spelled`; the proof of `nativeLawful` |
| `NativeOp.atLevel`, `NativeOp.atLevel_symm` | the same file | `nativeSignature`; `nativeProbes` of `tools/Drivers/ForeignCorpus.lean`, which performs a face as it stands; two guards of `Test/Codegen/ReadContract.lean`, rewritten |
| `FnName.decode?`, `FnName.totalName?`, `FnName.headName?`, and the theorems `headName?_image`, `image_injective`, `decode?_image`, `image_of_decode?` | `src/Effect4/Program/FnName.lean` | `termFace` and `atLevel`, both gone. One comment of `ts/eff/ingest/check-coverage.ts`, rewritten. The case policy `tools/Conform/Effect4/cases-policy.json`, which is stale now and not re-pinned |
| `Forms.lambdaShape`, `lambdaShape_atom`, `lambdaAtom_exact` | `src/Effect4/Codegen/Forms.lean` | `Styles.atom?`; `lambdaJs` of `tools/Drivers/TsGen.lean`; `Test/Codegen/FormsContract.lean`. Each reads `LambdaShape.term` now |
| `Styles.atom?` | `src/Effect4/Codegen/Styles.lean` | `Styles.expression`, under the `lambdas` style. It calls `restyleFunction`, which asks `lambdaOf` |
| `allFnNames`, `fnJs` | `tools/Drivers/TsGen.lean` | `lambdaJs` and `emitForms`, rewritten over `lambdaShapes` |
| `termAtLevel`, `opAtLevel`, `atNodeLevel` | `ts/eff/read.ts` | `readPerform`, rewritten |
| `opAt`, `lambdaAtom` | `ts/eff/ingest/ck.ts` | the row loop and the foreign branch, rewritten (`withTerm`, `rowFunction`, `lambdaShape`, `foreignFunction`) |
| `lambdaAtom` | `ts/eff/ingest/oxc.ts` | the row loop, rewritten (`rowFunction`, `lambdaShape`, `shapeTerm`) |
| The exports `incr`, `double`, `takeAndBump`, `zeroWhenPositive`, `noChange`, and six self-test rows | `harness/truth/prelude.ts` | three import headers: `harness/truth/run-truth.ts`, `harness/tsdiag/run-tsdiag.mjs`, `ts/eff/ingest/fidelity/roundtrip.ts` |

**Kept, because a reader remains.** The brief lists `LambdaShape` for deletion. I stopped that
deletion.

- `Forms.LambdaShape` and `lambdaAtom` stay. The foreign corpus still spells the four foreign
  lambdas (`tools/Drivers/Styles.lean`), and both foreign recognizers still read them
  (`forms.lambdas`). A shape now names the term that it spells at each row
  (`LambdaShape.term`).
- `FnName` stays as a library of terms, with `image`, `valueAt`, `fnNames` and `fnSpelling`.
  Its readers are the corpus generator (`Test/Program/Gen.lean`), the law `image_eval`
  (`src/Effect4/Laws/Program/Progress.lean`), `LambdaShape.term`, and five file names of the
  styles driver.
- `PrintRefusal.binderTerm` stays for one case: a value row that carries a term.

## 7. The two choices, and each other choice

1. **The parameter of a printed function (the brief's first choice).** tsgo 7 infers it at
   each of the eight rows, from the row's signature on the pin. Control:
   `harness/truth/term-rows.typecheck.ts` has one green line and one red line for each row.
   In each red line the one fault needs a number parameter, so a parameter of type `any` would
   pass it. With the sixteen directives removed, the compiler reports sixteen errors.
   **The fold with a stated type keeps its element at `any`.** The readers do not read a
   stated type, and Lean's checker types the element. The control holds one line that the
   target accepts and Lean refuses.
2. **A list of number literals (the brief's second choice).** One signature change repairs it,
   so I made it. `cons` is `<A, B = A>(x: A, xs: ReadonlyArray<B>): ReadonlyArray<A | B>`. The
   compiler infers the element from the element alone, and a literal widens. Control: two lists
   of different literals type-check together. Red control: the same file on the base prelude
   fails with four errors. One cost: the target no longer refuses a list of two unrelated
   element types. Lean's checker does, so no printed module holds one. The target lane still
   finds `cons` in agreement with its template at the probe.
3. **Where the function is read.** The brief places it in `readPerformFace`, `readRowCall` and
   `readRowMethod`. I placed it one layer out. `withFunction` appends the function to the
   printed row call, and `splitFunction` takes it off before the row is read. The accepted
   language is the same. The three readers and `printRow` keep their definitions, and their
   lemmas keep their statements up to the face.
4. **The spelled operation is a face.** `spell` answers a term row with the unit literal for
   its term (`Signature.face`). The reader installs the term it read. A row does not depend on
   its operation's term (`withTerm_row`).
5. **A term row without its function is refused, never read at its face.** A function on a
   row with no term is refused too. Both are `ReadRefusal.arity` with the row's spelling.
6. **The record collector reads an operation's term.** `classesOf` reads it through
   `ScopedOp.term?`, so `classesOf`, `roundTrip` and `readable` take `[ScopedOp Op]`. A class
   that only a term constructs is declared, and its module reads back. The battery holds the
   program, and a red control over an alphabet that shows no term.
7. **The names leave the foreign contract too.** A name in a function's place is refused by
   both recognizers (`E-ARG-CLOSURE`). Both read a function under any parameter name. The four
   lambda shapes stay, each with the term that it spells at each row. One spelling stays odd,
   as at the base: `(_) => Option.none()` on `Ref.update` reads as the identity. The foreign
   corpus lost 32 native probes in each of its 21 styles, so its pinned count moves to 22314.
8. **A term row is no callable adapter row.** `tools/Tools/RowTypes.lean` keeps its request
   column empty, as when the row carried a trailing name. The compiler control checks the
   eight signatures.
9. **The truth programs.** The brief names three.
   - *One `Ref.modify` whose term folds, with an outer capture:* `pModifyFold`. Lean and rc.112
     answer `[21, 7]`.
   - *The rate limiter's request:* held out of the lane. Its module ran on rc.112 with the
     machine's answer, `[true, false, 3, 1, 3]`, in a scratch copy of the lane. tsgo 7 refuses
     the module: `Type 'false' is not assignable to type 'true'`, once for each request. The
     battery pins the request's text, its program and the machine's answer
     (`fourRequests`).
   - *A `Deferred.make<void, never>` gate:* waits for part B.
   - *Added:* `pQueueOffer`, the probe's offer step, twice on the probe's first state. Lean and
     rc.112 answer `[false, 2, 0]`. The cell's printed type names `Deferred<void, never>`.
10. **A registered difference, with its control.** `pair` and `tuple` have `const` type
    parameters, so that a string literal keeps its literal type. The same modifier keeps a
    boolean and a number literal, where Lean types `bool` and `nat`. Two arms that Lean types
    alike can then be two target types. The control pins three such lines as refused. I
    tested a repair in a scratch copy and did not land it: it changes two atoms and three
    pins of `harness/truth/tuples.typecheck.ts` (item 11, row 3). The table gives each printed
    step under tsgo 7.0.0-dev.20260629.1, at the cell's printed type.

    | Printed text | Base prelude | New `cons` | New `cons`, literals widened at `pair` and `tuple` |
    | --- | --- | --- | --- |
    | The probe's offer step | accepted | accepted | accepted |
    | The probe's first take attempt | refused | refused | accepted |
    | The probe's later attempt | accepted | accepted | accepted |
    | The probe's withdrawal | accepted | accepted | accepted |
    | The real take step (9120 characters) | refused, 12 errors | refused, 12 errors | accepted |
    | The real offer step | accepted | accepted | accepted |
    | The model's `withdrawTake` | accepted | accepted | accepted |
    | The model's `withdrawOffer` | accepted | accepted | accepted |
    | The rate limiter's request | refused | refused | accepted |

    A conditional atom with two type parameters accepts the request and neither refused step.
    I did not land that either: it treats one symptom.
11. **Two pins in the dogfood files only.** In the four dogfood files I changed the pin lines
    and each battery's `stage`, as the brief says. Item 13 lists the lines there that are
    stale now.
12. **The generated groups follow in steps A5 to A7.** Steps A1 to A4 hold stale generated
    files. The head holds none that I know of.

## 8. The coordinator's four addenda

1. **Program `r4` joins the battery.** `Test/Codegen/TermRows.lean` copies `Steps` from
   `QueueSteps.lean`. `r4` builds, and the Lean machine answers `[true, 1, true, 2]`. Each of
   its four steps prints and reads back where it stands. Its module is pinned at
   `refused: typeSpelling Deferred.make`, as are `s9`, `s11` and `s12`. The take step has 765
   nodes and 11 folds. It prints to 9120 characters in 11 ms and reads back in 5 ms, in one
   interpreted run. tsgo compiles it with the prelude in under one second. Neither is slow.
2. **The annotation refusal, commit `cb9fcce9`.** An annotated function at a term row is
   refused as `ReadRefusal.annotation "<spelling> <site>"`. The two pinned refusals are
   `annotation "Ref.update parameter"` and `annotation "Ref.update return"`. A third is pinned
   beside them, `annotation "Ref.update thunk return"`. A missing function, a wrong binder and
   two parameters stay `arity "Ref.update"`, each with its own guard. The accepted domain did
   not move. The program that builds a tagged record only inside `Ref.modify` is `shortModule`
   in the battery.
3. **The tuple control, commit `23d7efbe`.** `scripts/check-truth.py` copies
   `tuples.typecheck.ts`. It refuses a plain file name of `include` that the work directory
   does not hold. The rule `$(CHK)/truth` takes the two tuple files as inputs. **Result of
   the tuple control:** it type-checks under tsgo 7.0.0-dev.20260629.1, inside
   `make check-truth`. Two red controls ran on temporary edits, which I removed again:
   - `FAIL truth: harness/truth/tsconfig.json includes absent.typecheck.ts, which the work
     directory does not hold; copy it beside the others`;
   - `FAIL truth: the regenerated modules do not type-check … tuples.typecheck.ts(31,7):
     error TS2322`.
4. **A term row with explicit type arguments, commit `2deea521`.** The prediction held, and I
   reproduced it before the correction.

   | Source | Compiler-backed reader | oxc reader |
   | --- | --- | --- |
   | Candidate, `Ref.update<number>(cell, (s) => succ(s))`, before | lifted | `E-NODE`, `fragment node: Ref.update` |
   | Candidate, after | `E-NODE`, `fragment node: Ref.update` | `E-NODE`, `fragment node: Ref.update` |
   | Positive, the same without `<number>`, before and after | lifted | lifted, to the same program |

   A term row declares no type argument, so the compiler-backed reader keeps the refusal.
   Neither reader drops the arguments. The control is in
   `ts/eff/ingest/test/foreign.test.ts`, with two more candidates. The same disagreement stood
   at the base for a lambda shape, `Ref.update<number>(cell, (x) => x + 1)`. I reproduced that
   on a scratch copy of the base's `ts/eff`.

## 9. Part B: where it stopped, and the design note

**Where it stopped.** Part B must read `Deferred.make<void, never>()` back to
`deferredMakeOf .unit .never`. That needs a map from target type syntax to `Ty`. The tree has
one such reader, `Classes.readTy` (`src/Effect4/Codegen/Classes.lean`), written for a payload
class's fields. A scratch probe ran it on the printed form of 27 types.

| The reader's answer on `Types.ofTy t` | The types `t` |
| --- | --- |
| `t` itself | `unit`, `bool`, `nat`, `string`, a literal, `option`, `list`, `prod`, a tuple, `except`, a map, `null`, `undefined`, `bytes`, an untagged record, a union |
| another type | `int` and `number`: both print `number`, which reads as `nat` |
| nothing | `never`, `unknown`, `refOf`, `deferredOf`, `exitOf`, `causeOf`, `fiberOf`, the scope handle, a tagged record |

The brief's own instance needs `never`, which the reader does not read. So part B needs a
reader that the tree does not have, and the brief says to stop there.

**One item of part B is already true.** No golden `.ty` verdict holds a spelled handle name.
Each holds the structural type, such as `["refOf",["nat"]]`.

**What the reader must read.** The printer writes a type at three sites, and the readers
refuse each one today. One reader serves all three.

| Site | Printed form | Today |
| --- | --- | --- |
| A row's type arguments | `Deferred.make<void, never>()` | the printer refuses another instance than `(nat, nat)`: `typeSpelling` |
| A loop's stated cursor type | `let a0: Option.Option<number> = none()` | printed; the reader answers `annotation "local const"` |
| A fold's stated accumulator type | `fold<B>(…)` | printed; the reader answers `annotation "fold accumulator"` |

The Queue needs the first two. Its hints are `Deferred<void, never>` and
`Deferred<boolean, never>`, and its take loop states the cursor type `Option<number>`. So the
Queue needs four type names read: `void`, `boolean`, `number`, `never`, and `Option.Option`.

**Its smallest form.** Two forms are possible. I recommend the first.

1. *Read the type syntax, and accept only what prints back.* Add one arm to
   `Classes.readNamed`: `never`. Define the reading of a type argument as `readTy x`, kept
   only when `Types.ofTy` of the answer is `x`. This is the class reader's own pattern
   (`readClassDecl`). Exactness then holds by definition. The retraction holds on a decidable
   domain, one check for each instance, and that check joins `rowDom`. The new arm changes no
   class: a payload record with a `never` field is not payload-admissible. An instance at
   `int` or `number` stays outside the domain, and so does an instance at a handle type until
   the reader gains that head.
2. *Carry the type as metadata in expression position.* `recordValue` does this for a
   record's declared type, and the pair `Metadata.writeTy` and `Metadata.readTy` is proved
   exact. It needs no reader of type syntax. It needs a prelude helper, because
   `Deferred.make` takes no argument, so the printed program would not call rc.112's export.

**Where the first form plugs in.** It follows part A's shape.

- The signature gains `typeArgsOf` and `withTypeArgs`, as it gained `withTerm`. `spell` answers
  the face. The reader reads the call's type arguments and installs them.
- The printer takes the type arguments from the operation and prints them with `Types.ofTy`.
  `PrintRefusal.typeSpelling` stays for a type with no printed form: a row template's
  parameter, a nominal application, a map whose key is no string, and a handle whose name does
  not parse.
- A bare `Deferred.make()` meets a face that carries type arguments, and the reader refuses
  it. It is never typed at a default.
- **One point is harder than in part A.** A term row does not depend on its term. A row does
  depend on its type arguments: `deferredMakeOf`'s answer column holds them. So the row lemmas
  of `src/Effect4/Laws/Codegen/ReadLeaf.lean` need restating over the columns that the reader
  reads: the spelling, the shape, the trailing names and the request.
- `Row.typeArgs` holds spelled strings today. Retyping it moves the row's wire form in every
  estate: the derived schema, `profile.gen.ts`, `corpus.json`'s host rows, the OCaml metadata
  and both foreign recognizers. The conservativity policy will meet it.
- `ts/eff/read.ts` has the reader's twin, `readTypeNode`. It keeps a call's type arguments as
  rendered strings today.

Part B is a slice of its own size. I did not start it.

## 10. Open obligations, and what the next two slices need

**Open.**

1. Part B, whole (item 9).
2. `Test/fixtures/target/selection.json` lacks `"pFold"`, and `make check-target` is red until
   it has it.
3. `tools/Conform/Effect4/cases-policy.json` holds eight stale sites.
4. The registered difference on the target (item 7.10).
5. The build ledger of the release lane is stale by three programs.
6. The conservativity policy has not met this slice: 39 printed programs, the foreign corpus,
   and `eff_native.ml`.

**What the Queue's slice needs from this one.**

- Each of the Queue's eight steps prints and reads back today, as a node. The battery holds
  them.
- Six of the eight type-check on the target today. The two others wait on the registered
  difference: the probe's first take attempt and the real take step.
- A Queue module needs part B for its hints, and the same reader for its take loop's cursor.
  After the hints, the cursor's annotation is the next refusal.
- `pQueueOffer` shows one step through the whole lane: printed, type-checked, run on rc.112,
  equal to the machine.

**What the mask's slice needs from this one.**

- `LawfulSpelling` has five more fields. An extended table whose new operations carry no term
  meets them by `rfl`.
- `readPerform` now takes a last argument `(aN) => body` off a row call, when `aN` is the
  binder due at the node's level. A new row that takes such a function as an ordinary argument
  would be refused. The mask's two printed rows are not of that shape, if each is a template of
  its own.
- The row table's premises are unchanged: `rowsApart`, `table_apart` and `table_shape`.

## 11. Proposed decisions rows (proposals only)

| # | Topic | Proposal |
| --- | --- | --- |
| 1 | T5, part A | Record it as landed: a binder term prints as a function on every face, and the five names spell nothing, in the foreign contract too. Amend rows 212 and 251 |
| 2 | Part B's reader | Choose form 1 of item 9: `Classes.readTy` with `never`, accepted only when it prints back. Dispatch part B as its own slice, with the loop's cursor and the fold's accumulator as its second and third consumers |
| 3 | Number and boolean literals at `pair` and `tuple` on the target | Widen them, as Lean's literal rule types them, and keep a string literal. Tested in a scratch copy: all eight steps, the request and all 42 truth modules type-check, and the only lines that fail are three pins of `harness/truth/tuples.typecheck.ts`. Or keep the literals and register the difference by a DI row. The three red lines of the compiler control move with the ruling |
| 4 | `cons` on the target | Ratify two type parameters and the union answer. The target then accepts a list of two unrelated element types, which Lean refuses |
| 5 | A fold with a stated type | Ratify option (a) of seat FOLD's proposal 2: the element stays `any` on the target, and Lean's checker types it. Part B's reader can make the stated type readable |
| 6 | The target selection | Add `"pFold"` between `"pInterruptEscape"` and `"pModifyFold"` |
| 7 | The case policy | Drop the eight sites of `FnName.totalName?` and `FnName.headName?` |
| 8 | The two foreign readers on an unmatched invocation | One code for both. Today both refuse `Ref.get(cell, 1)`, `Ref.get<number>(cell)` and `Deferred.make<string>()`, one with `E-ARG-DYNAMIC` and one with `E-NODE`. It stood at the base |
| 9 | The foreign lambda `(_) => Option.none()` on a total row | It reads as the identity on `Ref.update`, as at the base. Refuse the shape on a row whose function is total, or record why it stays |
| 10 | The rate limiter's request as a truth program | Add `Test.Codegen.TermRows.fourRequests` to the truth corpus when row 3 is ruled |
| 11 | `docs/STATE.md` | T5's part A landed; part B is a slice; the build ledger waits on three programs |

## 12. Bounded, host-only and unverified

- **Proved:** the theorems of item 5, for every program in their reach.
- **Bounded:** every `#guard` is one input. The forty images are checked at levels 0 to 3.
  The Queue's steps are checked at the one level where each stands.
- **Host-only:** the two truth programs' agreement with rc.112, under bun 1.4.2 on
  effect 4.0.0-rc.112; every tsgo verdict; the ingest gate's steps; the TypeScript reader
  lane.
- **Scratch evidence, not committed:** the table of item 7.10; the request's run on rc.112;
  the tested repair of row 3; the probe of `Classes.readTy`; the take step's times; the two
  foreign readers on a copy of the base. A later reader can repeat each from this receipt's
  text, and none is a fixture.
- **Built on three trees only.** The Lean build ran on step A1's tree, on step A4's tree and
  on the head's Lean tree. Steps A2, A3, A5, A6 and A7 were not built on their own.
- **Unverified:** each command of the "Not run" list. Among them: conservativity, the corpus
  lane, the slow lane, the release lane, the documents' references and the language rules. I
  ran the language checker on this slice's two document sections only.
- **Not established by any check:** that a host function printed from a term agrees with the
  term on every value. The truth lane compares finite runs.

## 13. Lines that are stale now, in files this seat may not edit

- `docs/STATE.md`: "The faces spell a term by one of five names and refuse any other. The
  faces of a binder term wait for T5."
- `Test/Dogfood/README.md`: the rows of p3, p4 and p5 say that the printer refuses a row by
  name (`binderTerm`) until T5, and so does the definition of `printed` in its table.
- `Test/Dogfood/Stage.lean`: the docstring of `printVerdict` says the same.
- `Test/Dogfood/P4RateLimiter.lean` and `Test/Dogfood/P5LedgerService.lean`: each header says
  that the stage loses `printed` until T5.
- `docs/core/decisions.md`, row 43: it describes the five-name alphabet as the current form.
- `docs/core/lcnf-route.md`: one line names the store functions `incr`, `double` and
  `takeAndBump`. It was stale before this slice.
- `tools/Effect4Gen/guards/program.lean`: one comment calls `succ(var 0)` "the name's image".
  It is still true. Changing it would move a derived file.
